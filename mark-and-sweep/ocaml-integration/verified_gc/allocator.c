/* allocator.c — Simple C free-list allocator for the verified GC.
 *
 * The heap is a contiguous byte array.  Objects are laid out as:
 *   [header (8 bytes)] [field_0 ... field_{wosize-1} (8 bytes each)]
 *
 * The free list is threaded through dead objects' first fields:
 *   free_head -> obj_A.field[0] -> obj_B.field[0] -> ... -> 0
 * Each pointer in the list is a VALUE address (header + 8).
 *
 * Allocation: first-fit walk of the free list.
 * If a free block is larger than needed, it is split.
 */

#include "allocator.h"
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

#define WORD_SIZE 8

static uint8_t *heap_base;
static size_t   heap_bytes;
static uint64_t free_head;   /* value address of first free block, or 0 */
static uint64_t bump_ptr;    /* next free byte for bump allocation */

/* ---------- helpers ---------------------------------------------------- */

static inline uint64_t read_word(uint8_t *base, uint64_t byte_off) {
    uint64_t v;
    memcpy(&v, base + byte_off, 8);
    return v;
}

static inline void write_word(uint8_t *base, uint64_t byte_off, uint64_t v) {
    memcpy(base + byte_off, &v, 8);
}

static inline uint64_t hdr_wosize(uint64_t hdr) {
    return hdr >> 10;
}

static inline uint64_t make_header(uint64_t wosize, uint64_t color, uint64_t tag) {
    return (wosize << 10) | (color << 8) | tag;
}

/* ---------- public API ------------------------------------------------- */

int allocator_init(size_t nbytes) {
    /* Round up to word boundary */
    nbytes = (nbytes + WORD_SIZE - 1) & ~(size_t)(WORD_SIZE - 1);
    heap_base = (uint8_t *)calloc(1, nbytes);
    if (!heap_base) return -1;
    heap_bytes = nbytes;

    /* Start as a single free block spanning the entire heap.
     * Header at offset 0, value at offset 8.
     * wosize = (nbytes / 8) - 1 (one word for the header). */
    size_t total_words = nbytes / WORD_SIZE;
    if (total_words < 2) { free(heap_base); return -1; }
    uint64_t wosize = total_words - 1;
    /* Color blue (2), tag 0 — blue marks free blocks */
    write_word(heap_base, 0, make_header(wosize, 2, 0));
    /* First field = 0 (end of free list) */
    write_word(heap_base, 8, 0);
    free_head = (uint64_t)(uintptr_t)(heap_base + 8);
    bump_ptr = 0; /* not used in free-list mode */
    return 0;
}

void *allocator_alloc(size_t wosize) {
    if (wosize == 0) wosize = 1; /* ensure at least 1 word for free-list link */

    uint64_t prev_val_addr = 0;
    uint64_t cur_val_addr = free_head;

    while (cur_val_addr != 0) {
        uint64_t hdr_addr = cur_val_addr - WORD_SIZE;
        uint8_t *hdr_ptr = (uint8_t *)(uintptr_t)hdr_addr;
        uint64_t hdr = read_word(hdr_ptr, 0);
        uint64_t blk_wosize = hdr_wosize(hdr);
        uint64_t next_val_addr;
        memcpy(&next_val_addr, (void *)(uintptr_t)cur_val_addr, 8);

        if (blk_wosize >= wosize) {
            size_t leftover = blk_wosize - wosize;
            if (leftover >= 2) {
                /* Split: shrink this block, create a new free block after it */
                /* New header for the allocated block */
                write_word(hdr_ptr, 0, make_header(wosize, 0, 0));

                /* Remainder block: header at hdr_addr + (1 + wosize) * 8 */
                uint64_t rem_hdr_addr = hdr_addr + (1 + wosize) * WORD_SIZE;
                uint8_t *rem_hdr_ptr = (uint8_t *)(uintptr_t)rem_hdr_addr;
                uint64_t rem_wosize = leftover - 1; /* one word for remainder header */
                write_word(rem_hdr_ptr, 0, make_header(rem_wosize, 2, 0));
                uint64_t rem_val_addr = rem_hdr_addr + WORD_SIZE;
                /* Link remainder to rest of free list */
                write_word(rem_hdr_ptr, WORD_SIZE, next_val_addr);

                /* Update previous link */
                if (prev_val_addr == 0)
                    free_head = rem_val_addr;
                else
                    write_word((uint8_t *)(uintptr_t)prev_val_addr, 0, rem_val_addr);
            } else {
                /* Use entire block (no split) */
                write_word(hdr_ptr, 0, make_header(blk_wosize, 0, 0));
                if (prev_val_addr == 0)
                    free_head = next_val_addr;
                else
                    write_word((uint8_t *)(uintptr_t)prev_val_addr, 0, next_val_addr);
            }
            /* Zero out the allocated fields */
            memset((void *)(uintptr_t)cur_val_addr, 0, wosize * WORD_SIZE);
            /* Return pointer to header */
            return (void *)(uintptr_t)hdr_addr;
        }

        prev_val_addr = cur_val_addr;
        cur_val_addr = next_val_addr;
    }

    return NULL; /* OOM — caller should trigger GC */
}

void allocator_set_freelist(uint64_t fp) {
    free_head = fp;
}

uint64_t allocator_get_freelist(void) {
    return free_head;
}

uint8_t *allocator_get_heap_base(void) {
    return heap_base;
}

size_t allocator_get_heap_size(void) {
    return heap_bytes;
}

uint64_t allocator_get_heap_end(void) {
    return (uint64_t)(uintptr_t)(heap_base + heap_bytes);
}
