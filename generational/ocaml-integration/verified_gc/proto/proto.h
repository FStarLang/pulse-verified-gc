/* proto.h — unverified C prototypes for the allocator comparison
 * (docs/allocator-comparison.md, section 6; results in
 * docs/allocator-comparison-results.md).  Measurement only.
 *
 * Two builds use these files, each with the hooked copy of the extracted
 * code that verified_gc/proto/hook_snapshot.py writes:
 *   -DVERGC_PROTO_A  A: the verified size-list allocator and fused sweep, plus
 *                    a parallel sweep cut by the object-start table and an
 *                    incremental sweep (sweep_lists.c);
 *   -DVERGC_PROTO_B  B: 32 KB pages by size class (alloc_pages.c).
 * The sweep mode is chosen at startup:
 *   VERGC_SWEEP=seq|par|incremental      (default seq)
 *   VERGC_PAR_SWEEP_THREADS=1..8         (default 4)
 *   VERGC_PROTO_STATS=1                  timers and counters on stderr at exit
 *   VERGC_PROTO_MEM=1                    also, at every major collection, the
 *                                        locality of pointers after the mark
 *                                        and where the heap's words go after
 *                                        the sweep (slow; not for timing)
 * With -DVERGC_PROTO_CHECK every sweep is compared with the verified
 * fused_sweep_coalesce run on a copy of the heap (proto_check.c), and
 * VERGC_PROTO_CHECK_CONTROL=1 runs a deliberately wrong sweep the check must
 * reject (=2: B2 and B3's large-object sweep instead). */
#ifndef VERGC_PROTO_H
#define VERGC_PROTO_H

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>
#include <stdio.h>
#include "GC_Gen_Impl.h"

/* The bridge's heap bounds (GC.Spec.ZeroAddr) and the extracted code's own
 * copies, assigned by krmlinit_globals(). */
extern uint64_t zero_addr, heap_size_u64;
extern uint64_t zero_addr1, heap_size_u640;

/* The verified code, kept under new names by hook_snapshot.py. */
uint64_t vergc_lists_allocate(heap_t heap, uint64_t *heads, uint64_t *tbl, uint64_t wosize);
void vergc_verified_fused_sweep(heap_t heap, uint64_t *heads, uint64_t *tbl);

#define PW(a)         (*(uint64_t *)(uintptr_t)(a))
#define HD_WZ(h)      ((h) >> 10)
#define HD_COL(h)     (((h) >> 8) & 3)
#define COL_BLUE      2ULL
#define COL_BLACK     3ULL
#define IS_BLACK(h)   (((h) & 0x300ULL) == 0x300ULL)
#define IS_BLUE(h)    (((h) & 0x300ULL) == 0x200ULL)
#define MK_BLUE(wz)   (((uint64_t)(wz) << 10) | (2ULL << 8))
#define WHITEN(h)     ((h) & ~0x300ULL)
#define N_LISTS       17           /* A: lists 1..16 exact, list 0 the rest */
#define TBL_SHIFT     16           /* A: one table entry per 64 KB window */
#define SLICE_WORDS   4096ULL      /* one incremental slice, both allocators */

enum { SW_SEQ = 0, SW_PAR = 1, SW_INCR = 2 };
enum { PK_SLICE = 0, PK_ALLOC = 1, PK_FINISH = 2, PK_N = 3 };

/* ---- proto_common.c ---------------------------------------------------- */
extern int       proto_mode;        /* SW_* */
extern int       proto_threads;
extern int       proto_check_control;
extern int       proto_stats;
extern int       proto_mem;
extern uint64_t *proto_heads;       /* A's 17 heads (unused by B) */
extern uint64_t *proto_tbl;         /* A's object-start table (unused by B) */
extern uint64_t  proto_tbl_len;

uint64_t proto_now(void);
/* Sweep work outside a collection: wrap it so the stop it happens in is
 * charged with it, by kind. */
void proto_sweep_work_begin(int kind);
void proto_sweep_work_end(int kind);
void proto_record_eager_sweep(uint64_t ns);
void proto_count(const char *name, uint64_t n);
/* VERGC_PROTO_MEM: call after the mark, before the sweep. */
void proto_mem_after_mark(void);

typedef void (*proto_job)(int i, int n, void *arg);
/* Run f(0..n-1) in parallel, f(0) on the calling thread; persistent
 * workers, started on first use. */
void proto_pool_run(int n, proto_job f, void *arg);
/* Run chunk(0..k-1) on n threads, each taking the next chunk from a shared
 * counter (dynamic balance).  CHUNKS_PER_THREAD chunks per thread. */
#define CHUNKS_PER_THREAD 8
#define MAX_CHUNKS (8 * CHUNKS_PER_THREAD)
void proto_pool_chunks(int n, int k, void (*chunk)(int c));

/* ---- par_mark_pages.c: the mark (VERGC_MARK=hdr|bm|bp) ------------------ */
extern int       proto_mark;        /* 0 header colours, else the bitmap */
extern uint32_t *proto_bm;          /* bit i: heap word zero_addr + 8 i */
extern int       proto_chunks_static;
extern int       proto_pool_record;
void proto_mark_stats(FILE *f);
#ifdef VERGC_PROTO_CHECK
void proto_mark_after_oracle(void);
void proto_mark_after_sweep(void);
#endif

/* ---- the allocator under test (alloc_pages.c or sweep_lists.c) ---------- */
void        impl_init(void);
const char *impl_name(void);
double      impl_consumption(void);      /* words used per word requested */
int         impl_sweeping(void);         /* an incremental sweep is open */
void        impl_slice(void);            /* sweep about SLICE_WORDS words */
double      impl_swept_fraction(void);
void        impl_finish(void);           /* close the open sweep */
void        impl_stats(FILE *f);
void        impl_check(const char *where);
void        impl_mem(void);              /* VERGC_PROTO_MEM, after an eager sweep */

/* ---- proto_check.c (VERGC_PROTO_CHECK only) ----------------------------- */
#ifdef VERGC_PROTO_CHECK
/* At the start of a sweep (after the mark): copy the heap and run the
 * verified sweep on the copy; it is the oracle until the next one. */
void chk_oracle(void);
/* Right after an eager sweep: survivors (non-blue blocks) and their contents
 * must equal the oracle's.  `exact` also compares the free blocks, the 17
 * lists and the table word for word (A's parallel sweep). */
void chk_compare_eager(const char *where, int exact);
/* Incremental: record the non-blue blocks of [a, b) before a unit of sweep;
 * after it, every recorded black block must be white with the same contents
 * and an oracle survivor, every recorded white block not one; `dead_blue`
 * also requires the dead ones to lie in a blue block already. */
void chk_unit_pre(uint64_t a, uint64_t b);
void chk_unit_post(const char *where, int dead_blue);
/* Every block allocated while a sweep is open. */
void chk_note_alloc(uint64_t hp);
/* When an incremental sweep closes: non-blue blocks = oracle survivors plus
 * blocks allocated since the oracle, and every survivor is intact. */
void chk_sweep_closed(const char *where);
void chk_fail(const char *where, const char *what, uint64_t a, uint64_t b);
/* Walk of [a, b): tiled exactly, each header inside. */
void chk_walk(const char *where, uint64_t a, uint64_t b);
#endif

#endif
