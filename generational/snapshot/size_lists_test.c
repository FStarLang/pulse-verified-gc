/* Size-segregated free lists: directed tests of the extracted `allocate`.
 *
 * Each test lays out a small heap by hand (zero_addr = 0, so offsets are
 * addresses), sets the list heads, allocates once, and checks the object, the
 * headers written and every head against GC.Spec.Allocator.Lists:
 * list w (1 <= w <= n_small) holds blocks of wosize w, list 0 larger ones;
 * a request tries list wz, then wz+1 .. n_small, then list 0; the object is
 * carved from the top of the block; a remainder of wosize >= 1 whose class
 * is not the list's moves to its own list; a wosize-0 remainder is on none.
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include "compat.h"
#include "GC_Gen_Impl.h"
#include "krmlinit.h"
#include "internal/GC_Gen_Impl.h"

/* GC.Spec.SizeClass.n_small_u64 + 1; the tests below pin the 16/17 cut-off. */
#define NL 17

static uint8_t *mem;
static heap_t heap;
static uint64_t heads[NL];
static int failures;

static void wr(uint64_t a, uint64_t v) { memcpy(mem + a, &v, 8); }
static uint64_t rd(uint64_t a) { uint64_t v; memcpy(&v, mem + a, 8); return v; }
static uint64_t hdr(uint64_t wz, uint64_t col) { return (wz << 10) | (col << 8); }
enum { WHITE = 0, BLUE = 2 };

/* Lay out blocks (wosize, colour) from address 0 and fill the rest of the
 * heap with one white block; objs[i] is block i's object address.  Free
 * blocks get a null link; every head is cleared. */
static void layout(int n, const uint64_t *wz, const uint64_t *col, uint64_t *objs) {
    memset(mem, 0, (size_t)heap_size_u64);
    memset(heads, 0, sizeof heads);
    uint64_t pos = 0;
    for (int i = 0; i < n; i++) {
        wr(pos, hdr(wz[i], col[i]));
        objs[i] = pos + 8;
        pos += (wz[i] + 1) * 8;
    }
    wr(pos, hdr((heap_size_u64 - pos) / 8 - 1, WHITE));
}

#define CHECK(name, cond) do { \
    if (!(cond)) { printf("FAIL: size lists: %s: %s\n", name, #cond); failures++; } \
} while (0)

static void heads_zero_except(const char *name, int a, int b) {
    for (int i = 0; i < NL; i++)
        if (i != a && i != b && heads[i] != 0) {
            printf("FAIL: size lists: %s: heads[%d] = %llu, expected 0\n",
                   name, i, (unsigned long long)heads[i]);
            failures++;
        }
}

int test_size_lists(void) {
    mem = calloc((size_t)heap_size_u64, 1);
    if (!mem) { perror("calloc"); return 1; }
    heap.data = mem;
    heap.size = (size_t)heap_size_u64;
    uint64_t o[4];

    /* exact hit: pop the head of list 5 */
    { uint64_t wz[] = {3, 5}, col[] = {WHITE, BLUE};
      layout(2, wz, col, o); heads[5] = o[1];
      uint64_t r = allocate(heap, heads, 5);
      CHECK("exact", r == o[1]);
      CHECK("exact", rd(o[1] - 8) == hdr(5, WHITE));
      heads_zero_except("exact", -1, -1); }

    /* fallback: list 12 serves 6 (lists 6..11 empty); the 5-word remainder
     * moves to list 5, linked to that list's old head (list 5 is below the
     * request, so the search never looks at it) */
    { uint64_t wz[] = {3, 12, 5}, col[] = {WHITE, BLUE, BLUE};
      layout(3, wz, col, o); heads[12] = o[1]; heads[5] = o[2];
      uint64_t r = allocate(heap, heads, 6);
      CHECK("fallback", r == o[1] + 6 * 8);
      CHECK("fallback", rd(r - 8) == hdr(6, WHITE));
      CHECK("fallback", rd(o[1] - 8) == hdr(5, BLUE));
      CHECK("fallback", heads[5] == o[1] && rd(o[1]) == o[2]);
      heads_zero_except("fallback", 5, -1); }

    /* the smallest fitting list wins: lists 5 and 9 both fit 3; list 5 is
     * taken, and its 1-word remainder moves to list 1 */
    { uint64_t wz[] = {3, 9, 5}, col[] = {WHITE, BLUE, BLUE};
      layout(3, wz, col, o); heads[9] = o[1]; heads[5] = o[2];
      uint64_t r = allocate(heap, heads, 3);
      CHECK("smallest-list", r == o[2] + 2 * 8);
      CHECK("smallest-list", rd(o[2] - 8) == hdr(1, BLUE));
      CHECK("smallest-list", heads[1] == o[2] && heads[9] == o[1]);
      heads_zero_except("smallest-list", 1, 9); }

    /* fallback to a fragment: list 4 serves 3; the header-only remainder is
     * on no list */
    { uint64_t wz[] = {3, 4}, col[] = {WHITE, BLUE};
      layout(2, wz, col, o); heads[4] = o[1];
      uint64_t r = allocate(heap, heads, 3);
      CHECK("fragment", r == o[1] + 8);
      CHECK("fragment", rd(o[1] - 8) == hdr(0, BLUE));
      CHECK("fragment", rd(o[1]) == hdr(3, WHITE));
      heads_zero_except("fragment", -1, -1); }

    /* large to small: a 20-word block serves 3 and its 16-word remainder
     * leaves list 0 for list 16 */
    { uint64_t wz[] = {3, 20}, col[] = {WHITE, BLUE};
      layout(2, wz, col, o); heads[0] = o[1];
      uint64_t r = allocate(heap, heads, 3);
      CHECK("large-to-small", r == o[1] + 17 * 8);
      CHECK("large-to-small", rd(o[1] - 8) == hdr(16, BLUE));
      CHECK("large-to-small", heads[16] == o[1] && rd(o[1]) == 0);
      heads_zero_except("large-to-small", 16, -1); }

    /* large stays: a 40-word block keeps its 36-word remainder on list 0 */
    { uint64_t wz[] = {3, 40}, col[] = {WHITE, BLUE};
      layout(2, wz, col, o); heads[0] = o[1];
      uint64_t r = allocate(heap, heads, 3);
      CHECK("large-stays", r == o[1] + 37 * 8);
      CHECK("large-stays", rd(o[1] - 8) == hdr(36, BLUE));
      CHECK("large-stays", heads[0] == o[1]);
      heads_zero_except("large-stays", 0, -1); }

    /* a relist behind a predecessor: list 0 = [A(18), B(25)]; 20 words come
     * from B, whose 4-word remainder moves to list 4 and A links past it */
    { uint64_t wz[] = {18, 3, 25}, col[] = {BLUE, WHITE, BLUE};
      layout(3, wz, col, o); heads[0] = o[0]; wr(o[0], o[2]);
      uint64_t r = allocate(heap, heads, 20);
      CHECK("predecessor", r == o[2] + 5 * 8);
      CHECK("predecessor", rd(o[2] - 8) == hdr(4, BLUE));
      CHECK("predecessor", heads[0] == o[0] && rd(o[0]) == 0);
      CHECK("predecessor", heads[4] == o[2]);
      heads_zero_except("predecessor", 0, 4); }

    /* out of memory: only a 2-word block; nothing changes */
    { uint64_t wz[] = {3, 2}, col[] = {WHITE, BLUE};
      layout(2, wz, col, o); heads[2] = o[1];
      uint8_t *before = malloc((size_t)heap_size_u64);
      memcpy(before, mem, (size_t)heap_size_u64);
      uint64_t r = allocate(heap, heads, 3);
      CHECK("oom", r == 0);
      CHECK("oom", memcmp(before, mem, (size_t)heap_size_u64) == 0);
      CHECK("oom", heads[2] == o[1]);
      heads_zero_except("oom", 2, -1);
      free(before); }

    /* drained lists: lists 1..6 empty, list 7 serves 1 */
    { uint64_t wz[] = {3, 7}, col[] = {WHITE, BLUE};
      layout(2, wz, col, o); heads[7] = o[1];
      uint64_t r = allocate(heap, heads, 1);
      CHECK("drained", r == o[1] + 6 * 8);
      CHECK("drained", heads[5] == o[1]);
      heads_zero_except("drained", 5, -1); }

    /* the exact list is preferred to list 0 */
    { uint64_t wz[] = {3, 100}, col[] = {BLUE, BLUE};
      layout(2, wz, col, o); heads[3] = o[0]; heads[0] = o[1];
      uint64_t r = allocate(heap, heads, 3);
      CHECK("exact-first", r == o[0]);
      CHECK("exact-first", heads[0] == o[1]);
      heads_zero_except("exact-first", 0, -1); }

    free(mem);
    if (failures == 0) printf("size lists: all tests passed.\n");
    return failures;
}
