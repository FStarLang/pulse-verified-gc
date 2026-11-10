/* What alloc_pages.c needs from proto_common.c, for the eager sequential
 * sweep only (no stats, no checks, no threads). */
#include "proto.h"
#include <time.h>

int       proto_mode = SW_SEQ;
int       proto_threads = 1;
int       proto_check_control = 0;
int       proto_stats = 0;
int       proto_mem = 0;
uint64_t  zero_addr, heap_size_u64;

uint64_t proto_now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint64_t)ts.tv_sec * 1000000000ULL + (uint64_t)ts.tv_nsec;
}
void proto_sweep_work_begin(int kind) { (void)kind; }
void proto_sweep_work_end(int kind) { (void)kind; }
void proto_record_eager_sweep(uint64_t ns) { (void)ns; }
void proto_count(const char *name, uint64_t n) { (void)name; (void)n; }
void proto_mem_after_mark(void) {}
void proto_pool_chunks(int n, int k, void (*chunk)(int c)) {
    (void)n;
    for (int c = 0; c < k; c++) chunk(c);
}
