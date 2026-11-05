/* The object-start table: directed tests of the extracted `allocate`,
 * `table_rebuild` and the collectors' table writes.
 *
 * The table has one entry per 64 KB window of the major heap.  It is always
 * sound (GC.Spec.ObjectTable.table_sound; `ot_sound`): every entry is a
 * header of the heap walk at or below its window's boundary
 * zero_addr + j * 0x10000, and the entries do not decrease.  After a rebuild,
 * and after an allocation from an exact table, it is exact (table_ok, option
 * A3 of docs/allocator-table-and-size-lists.md; `ot_check`): entry j names
 * the walk block that contains boundary j.  zero_addr = 0 here, so offsets
 * are addresses.
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include "compat.h"
#include "GC_Gen_Impl.h"
#include "krmlinit.h"
#include "internal/GC_Gen_Impl.h"

#define NL 17
#define WIN 0x10000ULL

uint64_t ot_len(void) { return (heap_size_u64 - zero_addr + WIN - 1) / WIN; }

/* The number of entries of `tbl` that do not name the walk block containing
 * their boundary (a boundary past a walk that stops short names the last
 * block).  -1 if the walk itself is broken. */
long ot_check(const uint8_t *m, const uint64_t *tbl) {
    uint64_t nt = ot_len(), k = 0, pos = zero_addr, last = zero_addr;
    long bad = 0;
    while (pos + 8 < heap_size_u64) {
        uint64_t h; memcpy(&h, m + pos, 8);
        uint64_t next = pos + ((h >> 10) + 1) * 8;
        if (next > heap_size_u64 || next <= pos) return -1;
        for (; k < nt && zero_addr + k * WIN < next; k++)
            if (tbl[k] != pos) bad++;
        last = pos;
        pos = next;
    }
    for (; k < nt; k++) if (tbl[k] != last) bad++;
    return bad;
}

/* The number of entries of `tbl` that break soundness: not a header of the
 * walk, above the boundary, or below the entry before.  -1 if the walk itself
 * is broken. */
long ot_sound(const uint8_t *m, const uint64_t *tbl) {
    uint64_t nt = ot_len(), pos = zero_addr;
    uint64_t words = (heap_size_u64 - zero_addr) / 8;
    uint8_t *hd = calloc((size_t)words, 1);
    if (!hd) return -1;
    while (pos + 8 < heap_size_u64) {
        uint64_t h; memcpy(&h, m + pos, 8);
        uint64_t next = pos + ((h >> 10) + 1) * 8;
        if (next > heap_size_u64 || next <= pos) { free(hd); return -1; }
        hd[(pos - zero_addr) / 8] = 1;
        pos = next;
    }
    long bad = 0;
    for (uint64_t k = 0; k < nt; k++) {
        uint64_t e = tbl[k];
        if (e < zero_addr || e >= heap_size_u64 || (e - zero_addr) % 8 != 0 ||
            !hd[(e - zero_addr) / 8] || e > zero_addr + k * WIN ||
            (k > 0 && tbl[k - 1] > e))
            bad++;
    }
    free(hd);
    return bad;
}

static uint8_t *mem;
static heap_t heap;
static uint64_t heads[NL];
static uint64_t tbl[64];
static int failures;

static void wr(uint64_t a, uint64_t v) { memcpy(mem + a, &v, 8); }
static uint64_t rd(uint64_t a) { uint64_t v; memcpy(&v, mem + a, 8); return v; }
static uint64_t hdr(uint64_t wz, uint64_t col) { return (wz << 10) | (col << 8); }
enum { WHITE = 0, BLUE = 2 };

#define CHECK(name, cond) do { \
    if (!(cond)) { printf("FAIL: object table: %s: %s\n", name, #cond); failures++; } \
} while (0)

/* Blocks (wosize, colour) from address 0, the rest of the heap one white
 * block, then the verified rebuild of the table; all heads cleared. */
static void layout(int n, const uint64_t *wz, const uint64_t *col, uint64_t *objs) {
    memset(mem, 0, (size_t)heap_size_u64);
    memset(heads, 0, sizeof heads);
    for (int i = 0; i < 64; i++) tbl[i] = 0xdeadbeefULL;
    uint64_t pos = 0;
    for (int i = 0; i < n; i++) {
        wr(pos, hdr(wz[i], col[i]));
        objs[i] = pos + 8;
        pos += (wz[i] + 1) * 8;
    }
    if (pos < heap_size_u64) wr(pos, hdr((heap_size_u64 - pos) / 8 - 1, WHITE));
    table_rebuild(heap, tbl);
}

int test_object_table(void) {
    mem = calloc((size_t)heap_size_u64, 1);
    if (!mem) { perror("calloc"); return 1; }
    heap.data = mem;
    heap.size = (size_t)heap_size_u64;
    uint64_t o[4];
    const uint64_t W = WIN / 8;          /* words per window */
    uint64_t nt = ot_len();
    CHECK("windows", nt == 16 && nt <= 64);

    /* the rebuild of a laid-out heap: a block straddling boundary 1 */
    { uint64_t wz[] = {W - 10, 30}, col[] = {WHITE, BLUE};
      layout(2, wz, col, o);
      CHECK("rebuild", ot_check(mem, tbl) == 0);
      CHECK("rebuild", tbl[0] == 0 && tbl[1] == o[1] - 8); }

    /* a small object carved from the top of a block that straddles a
     * boundary: the object contains it, so entry 1 moves to it */
    { uint64_t wz[] = {W - 10, 30}, col[] = {WHITE, BLUE};
      layout(2, wz, col, o); heads[0] = o[1];
      uint64_t r = allocate(heap, heads, tbl, 25);
      CHECK("carve-over-boundary", r == o[1] + 5 * 8);
      CHECK("carve-over-boundary", tbl[1] == r - 8);
      CHECK("carve-over-boundary", ot_check(mem, tbl) == 0); }

    /* ... and one that does not contain the boundary: the remainder keeps it */
    { uint64_t wz[] = {W - 30, 60}, col[] = {WHITE, BLUE};
      layout(2, wz, col, o); heads[0] = o[1];
      uint64_t r = allocate(heap, heads, tbl, 20);
      CHECK("carve-below-boundary", r == o[1] + 40 * 8);
      CHECK("carve-below-boundary", tbl[1] == o[1] - 8);
      CHECK("carve-below-boundary", ot_check(mem, tbl) == 0); }

    /* an object exactly at a boundary: entry 1 names it */
    { uint64_t wz[] = {W - 22, 40}, col[] = {WHITE, BLUE};
      layout(2, wz, col, o); heads[0] = o[1];
      /* block 1 header at 8*(W-21); object header lands at 0x10000 */
      uint64_t r = allocate(heap, heads, tbl, 19);
      CHECK("at-boundary", r - 8 == WIN);
      CHECK("at-boundary", tbl[1] == WIN);
      CHECK("at-boundary", ot_check(mem, tbl) == 0); }

    /* a large object over three boundaries: one write per window */
    { uint64_t wz[] = {10, 4 * W}, col[] = {WHITE, BLUE};
      layout(2, wz, col, o); heads[0] = o[1];
      uint64_t r = allocate(heap, heads, tbl, 3 * W);
      CHECK("large", r != 0);
      CHECK("large", tbl[2] == r - 8 && tbl[3] == r - 8 && tbl[4] == r - 8);
      CHECK("large", ot_check(mem, tbl) == 0); }

    /* the last block of the heap: its object runs to the end, every boundary
     * from it on names it */
    { uint64_t wz[] = {10}, col[] = {WHITE};
      layout(1, wz, col, o);
      /* the trailing white block becomes a free block on list 0 */
      wr(o[0] + 10 * 8, rd(o[0] + 10 * 8) | (BLUE << 8));
      heads[0] = o[0] + 11 * 8; wr(heads[0], 0);
      uint64_t r = allocate(heap, heads, tbl, 2 * W);
      CHECK("last-block", r != 0 && r + 2 * W * 8 == heap_size_u64);
      CHECK("last-block", ot_check(mem, tbl) == 0); }

    /* an exact fit straddling a boundary changes no entry */
    { uint64_t wz[] = {W - 5, 10}, col[] = {WHITE, BLUE};
      layout(2, wz, col, o); heads[10] = o[1];
      uint64_t before[64]; memcpy(before, tbl, sizeof tbl);
      uint64_t r = allocate(heap, heads, tbl, 10);
      CHECK("exact-straddle", r == o[1]);
      CHECK("exact-straddle", memcmp(before, tbl, sizeof tbl) == 0);
      CHECK("exact-straddle", ot_check(mem, tbl) == 0); }

    /* out of memory writes nothing */
    { uint64_t wz[] = {W - 5, 2}, col[] = {WHITE, BLUE};
      layout(2, wz, col, o); heads[2] = o[1];
      uint64_t before[64]; memcpy(before, tbl, sizeof tbl);
      uint64_t r = allocate(heap, heads, tbl, 3);
      CHECK("oom", r == 0);
      CHECK("oom", memcmp(before, tbl, sizeof tbl) == 0); }

    /* A block re-tiled behind the allocator's back, as runtime/intern.c does
     * when it unmarshals into one major block: A = [0x8000, 0x38000) holds
     * boundaries 1-3 and is cut into A1, a free block F = [0x12000, 0x22000)
     * and A3.  The table stays sound but no longer exact: entries 2 and 3
     * still name A. */
    { uint64_t wz[] = {W / 2 - 1, 3 * W - 1}, col[] = {WHITE, WHITE};
      layout(2, wz, col, o);
      CHECK("retile", tbl[1] == 0x8000 && tbl[2] == 0x8000 && tbl[3] == 0x8000);
      wr(0x8000, hdr((0x12000 - 0x8000) / 8 - 1, WHITE));
      wr(0x12000, hdr(0x10000 / 8 - 1, BLUE));
      wr(0x22000, hdr((0x38000 - 0x22000) / 8 - 1, WHITE));
      CHECK("retile", ot_check(mem, tbl) == 2);
      CHECK("retile", ot_sound(mem, tbl) == 0);
      /* An object carved from the top of F contains boundary 2, but entry 3,
       * past it, names A, below the object: writing entry 2 would break (M),
       * so the guard writes nothing. */
      heads[0] = 0x12008; wr(0x12008, 0);
      uint64_t before[64]; memcpy(before, tbl, sizeof tbl);
      uint64_t r = allocate(heap, heads, tbl, W / 2);
      CHECK("guard", r == 0x22000 - W / 2 * 8);
      CHECK("guard", memcmp(before, tbl, sizeof tbl) == 0);
      CHECK("guard", ot_sound(mem, tbl) == 0);
      /* the rebuild restores exactness */
      table_rebuild(heap, tbl);
      CHECK("retile-rebuild", ot_check(mem, tbl) == 0 && tbl[2] == r - 8); }

    /* The sweep's rebuild (C3): dead D1 = [0, 0xFFE0) and dead D2, whose
     * header 0xFFE0 is the last one below boundary 1, coalesce with the rest
     * into one run from 0.  D2's header is absorbed, so entry 1 is 0, the
     * run's header, not 0xFFE0. */
    { uint64_t wz[] = {0xFFE0 / 8 - 1, 7}, col[] = {WHITE, WHITE};
      layout(2, wz, col, o);
      CHECK("sweep-absorbs", tbl[1] == 0xFFE0);
      uint64_t gray[16]; size_t top = 16;
      gray_stack_rec st = { .storage = gray, .top = &top, .cap = 16 };
      collect(heap, st, heads, tbl);
      CHECK("sweep-absorbs", tbl[1] == 0);
      CHECK("sweep-absorbs", ot_check(mem, tbl) == 0);
      CHECK("sweep-absorbs", ot_sound(mem, tbl) == 0); }

    free(mem);
    if (failures == 0) printf("object table: all tests passed.\n");
    return failures;
}
