/* alloc.c — Bridge between OCaml 4.14 runtime and the verified GC.
 *
 * Provides:
 *   verified_allocate(wosize)       — called from OCaml's Alloc_small / caml_alloc_shr
 *   caml_trigger_verified_gc(unit)  — OCaml-callable GC trigger
 *
 * Uses:
 *   collect() from GC_Impl.c        — verified mark-and-sweep
 *   allocator from allocator.c       — C free-list allocator
 *   caml_do_roots() from OCaml       — root scanning
 *
 * NULL-base trick: the verified GC uses byte-offset addressing with heap.data
 * as the base pointer. We set heap.data = NULL so that byte offsets become
 * absolute virtual addresses. This avoids translating between OCaml's absolute
 * pointers and the GC's offset-based model.
 *
 * Requires three patches to GC_Impl.c:
 *   1. zero_addr = heap_start (absolute) instead of 0
 *   2. is_pointer: lower-bound check (v >= zero_addr + 8)
 *   3. darken_if_white: non-static
 */

#include "GC_Impl.h"
#include "allocator.h"
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

#ifndef CAML_INTERNALS
#define CAML_INTERNALS
#endif
#include "../caml/misc.h"
#include "../caml/mlvalues.h"
#include "../caml/roots.h"

/* Patched externs from GC_Impl.c */
extern void     darken_if_white(heap_t heap, gray_stack_rec st, uint64_t h_addr);
extern uint64_t zero_addr;

/* Storage for heap_size_u64 (declared extern in GC_Impl internal header) */
uint64_t heap_size_u64 = 0;

/* ---- Globals for root scanning ---------------------------------------- */

static heap_t         gc_heap;
static gray_stack_rec gc_stack;

/* ---- Heap initialization ---------------------------------------------- */

/* Default heap: 256 MB.  Override via MIN_EXPANSION_WORDSIZE env var
 * (value is in WORDS; we multiply by 8 to get bytes). */
static int  heap_initialized = 0;

static void ensure_heap(void) {
    if (heap_initialized) return;
    heap_initialized = 1;

    size_t heap_words = 32 * 1024 * 1024; /* 256 MB / 8 = 32M words */
    const char *env = getenv("MIN_EXPANSION_WORDSIZE");
    if (env) {
        size_t w = (size_t)atoll(env);
        if (w > 0) heap_words = w;
    }

    size_t heap_bytes = heap_words * 8;
    if (allocator_init(heap_bytes) != 0)
        caml_fatal_error("verified GC: cannot allocate heap");

    /* NULL-base trick: GC sees absolute addresses as "offsets" */
    uint8_t *base = allocator_get_heap_base();
    zero_addr     = (uint64_t)(uintptr_t)base;
    heap_size_u64 = (uint64_t)(uintptr_t)(base + heap_bytes);
}

/* ---- Root scanning callback ------------------------------------------- */

static void darken_root(value root, value *root_ptr) {
    (void)root_ptr;
    if (Is_block(root) && Wosize_val(root) > 0 &&
        (uint64_t)(uintptr_t)root >= zero_addr + 8 &&
        (uint64_t)(uintptr_t)root < heap_size_u64)
    {
        /* h_addr = absolute address of header = value - 8 */
        uint64_t h_addr = (uint64_t)(uintptr_t)Hp_val(root);
        darken_if_white(gc_heap, gc_stack, h_addr);
    }
}

/* ---- GC cycle --------------------------------------------------------- */

static void verified_gc(void) {
    ensure_heap();
    caml_gc_message(0x20, "Verified GC: collecting\n");
    Caml_state->_stat_major_collections++;

    /* NULL-base: heap.data = NULL, so GC accesses absolute addresses */
    gc_heap.data = NULL;
    gc_heap.size = allocator_get_heap_size();

    /* Allocate gray stack */
    size_t gray_cap = allocator_get_heap_size() / 64;
    if (gray_cap < 4096) gray_cap = 4096;
    uint64_t *gray_storage = (uint64_t *)calloc(gray_cap, sizeof(uint64_t));
    size_t gray_top = 0;
    if (!gray_storage)
        caml_fatal_error("verified GC: cannot allocate gray stack");

    gc_stack.storage = gray_storage;
    gc_stack.top     = &gray_top;
    gc_stack.cap     = gray_cap;

    /* Scan roots — pushes live object headers onto the gray stack */
    caml_do_roots(darken_root, 1);

    /* Current free-list head (absolute value address, or 0) */
    uint64_t fp = allocator_get_freelist();

    /* Run verified mark-and-sweep */
    uint64_t new_fp = collect(gc_heap, gc_stack, fp);

    /* Update allocator's free list */
    allocator_set_freelist(new_fp);

    free(gray_storage);
}

/* ---- Allocation entry point ------------------------------------------- */

void *verified_allocate(mlsize_t wosize) {
    ensure_heap();

    void *mem = allocator_alloc(wosize);
    if (mem) return mem;

    /* OOM — try GC */
    verified_gc();
    mem = allocator_alloc(wosize);
    if (mem) return mem;

    /* Still OOM — fatal */
    caml_fatal_error("verified GC: out of memory after collection");
    return NULL; /* unreachable */
}

/* ---- OCaml primitive -------------------------------------------------- */

CAMLprim value caml_trigger_verified_gc(value v) {
    (void)v;
    verified_gc();
    return Val_unit;
}
