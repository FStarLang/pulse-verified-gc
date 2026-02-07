/**
 * runtime_integration.h - OCaml Runtime Integration for Verified Concurrent GC
 *
 * This header defines the integration points between the verified concurrent GC
 * (extracted from Pulse) and the OCaml 4.14 runtime.
 *
 * Integration points:
 * 1. caml_modify - Needs write barrier hook
 * 2. caml_alloc - Needs allocation tracking
 * 3. Thread creation - Needs shadow stack registration
 * 4. GC trigger - Needs concurrent GC entry point
 */

#ifndef VERIFIED_GC_RUNTIME_INTEGRATION_H
#define VERIFIED_GC_RUNTIME_INTEGRATION_H

#include <stdint.h>
#include <stdbool.h>
#include <stdatomic.h>

/* =========================================================================
 * Include verified GC atomics
 * ========================================================================= */

#include "atomics.h"

/* =========================================================================
 * OCaml Value Types (from caml/mlvalues.h)
 * ========================================================================= */

typedef intnat value;
typedef uintnat header_t;
typedef uintnat mlsize_t;

/* =========================================================================
 * Verified GC State
 * ========================================================================= */

/**
 * GC phase enumeration
 * Corresponds to Pulse.Lib.GC.gc_phase
 */
typedef enum {
    GC_PHASE_IDLE = 0,
    GC_PHASE_MARKING = 1,
    GC_PHASE_SWEEPING = 2
} gc_phase_t;

/**
 * Global GC state
 * Corresponds to Pulse.Lib.GC.gc_state
 */
typedef struct {
    _Atomic gc_phase_t phase;          /* Current GC phase */
    void *gray_stack;                   /* Gray object stack */
    void *free_list;                    /* Free list head */
    _Atomic bool barrier_active;        /* STW barrier flag */
    void *shadow_registry;              /* Shadow stack registry */
    _Atomic uint64_t gc_cycle_count;   /* Number of GC cycles completed */
    _Atomic uint64_t bytes_allocated;   /* Total bytes allocated */
    _Atomic uint64_t bytes_reclaimed;   /* Total bytes reclaimed */
} verified_gc_state_t;

/**
 * Global GC state instance
 */
extern verified_gc_state_t verified_gc_state;

/* =========================================================================
 * Shadow Stack API (Per-Thread Root Registration)
 * ========================================================================= */

/**
 * Shadow stack entry
 * Each entry is a pointer to a GC root (value*)
 */
typedef struct shadow_stack_entry {
    value *root_ptr;
    struct shadow_stack_entry *next;
} shadow_stack_entry_t;

/**
 * Shadow stack for a mutator thread
 * Corresponds to Pulse.Lib.GC.RootScanning.shadow_stack
 */
typedef struct {
    _Atomic(shadow_stack_entry_t *) head;  /* Stack head (atomic for GC reads) */
    uint64_t thread_id;                     /* Owner thread ID */
    _Atomic bool active;                    /* Is thread active? */
} shadow_stack_t;

/**
 * Thread-local shadow stack
 */
extern __thread shadow_stack_t *tls_shadow_stack;

/**
 * Initialize shadow stack for current thread
 */
static inline void verified_gc_init_thread(void) {
    shadow_stack_t *ss = (shadow_stack_t *)malloc(sizeof(shadow_stack_t));
    atomic_init(&ss->head, NULL);
    ss->thread_id = (uint64_t)pthread_self();
    atomic_init(&ss->active, true);
    tls_shadow_stack = ss;
    /* Register with global registry */
    /* verified_gc_register_shadow_stack(ss); */
}

/**
 * Register a root with the shadow stack
 * Called when a local root is pushed (CAMLlocal)
 */
static inline void verified_gc_push_root(value *root_ptr) {
    shadow_stack_entry_t *entry = 
        (shadow_stack_entry_t *)malloc(sizeof(shadow_stack_entry_t));
    entry->root_ptr = root_ptr;
    
    shadow_stack_entry_t *old_head;
    do {
        old_head = atomic_load_explicit(&tls_shadow_stack->head, 
                                        memory_order_relaxed);
        entry->next = old_head;
    } while (!atomic_compare_exchange_weak_explicit(
        &tls_shadow_stack->head,
        &old_head,
        entry,
        memory_order_release,
        memory_order_relaxed));
}

/**
 * Unregister a root from the shadow stack
 * Called when a local root is popped (CAMLreturn)
 */
static inline void verified_gc_pop_root(void) {
    shadow_stack_entry_t *head = 
        atomic_load_explicit(&tls_shadow_stack->head, memory_order_acquire);
    if (head != NULL) {
        /* For simplicity, just remove head (LIFO order) */
        atomic_store_explicit(&tls_shadow_stack->head, head->next, 
                              memory_order_release);
        free(head);
    }
}

/* =========================================================================
 * Write Barrier API
 * ========================================================================= */

/**
 * Dijkstra write barrier implementation
 * 
 * Called BEFORE writing a pointer value to a field.
 * If source is black and target is white, grays the target.
 * 
 * Corresponds to Pulse.Lib.GC.write_with_barrier
 * 
 * @param src_addr Address of source object (containing the field)
 * @param dst_addr Address of destination object (being pointed to)
 */
static inline void verified_gc_write_barrier(value src_addr, value dst_addr) {
    /* Only active during marking phase */
    if (atomic_load_explicit(&verified_gc_state.phase, memory_order_acquire) 
        != GC_PHASE_MARKING) {
        return;
    }
    
    /* Get header addresses */
    header_t *src_hdr = (header_t *)(src_addr - sizeof(header_t));
    header_t *dst_hdr = (header_t *)(dst_addr - sizeof(header_t));
    
    /* Read source color */
    uint64_t src_color = gc_read_color((volatile uint64_t *)src_hdr);
    
    if (src_color == GC_COLOR_BLACK) {
        /* Source is black, check destination */
        uint64_t dst_color = gc_read_color((volatile uint64_t *)dst_hdr);
        
        if (dst_color == GC_COLOR_WHITE) {
            /* CAS destination from white to gray */
            if (gc_cas_color((volatile uint64_t *)dst_hdr, 
                            GC_COLOR_WHITE, GC_COLOR_GRAY)) {
                /* CAS succeeded, push to gray stack */
                /* verified_gc_push_gray(dst_addr); */
            }
            /* If CAS failed, another thread already grayed it */
        }
    }
}

/* =========================================================================
 * Allocation API
 * ========================================================================= */

/**
 * Allocate with write barrier awareness
 * New objects start as white.
 *
 * @param wosize Size in words
 * @param tag Object tag
 * @return Allocated value, or 0 if allocation failed
 */
static inline value verified_gc_alloc(mlsize_t wosize, int tag) {
    /* Get block from free list */
    /* This would call the extracted alloc_from_free_list */
    
    /* For now, placeholder */
    return 0;
}

/* =========================================================================
 * Safepoint API
 * ========================================================================= */

/**
 * Check for GC safepoint
 * Called at function entry/exit or loop back-edges
 * If sweep is active, blocks until sweep completes.
 */
static inline void verified_gc_safepoint(void) {
    /* Check if STW barrier is active */
    if (atomic_load_explicit(&verified_gc_state.barrier_active, 
                             memory_order_acquire)) {
        /* Wait at barrier */
        while (atomic_load_explicit(&verified_gc_state.barrier_active,
                                    memory_order_acquire)) {
            /* Yield to other threads */
            #if defined(__x86_64__) || defined(__i386__)
            __asm__ __volatile__("pause" ::: "memory");
            #elif defined(__aarch64__)
            __asm__ __volatile__("yield" ::: "memory");
            #endif
        }
    }
}

/* =========================================================================
 * GC Entry Points
 * ========================================================================= */

/**
 * Initialize the verified GC
 * Called once at program start.
 *
 * @param heap_size Initial heap size in bytes
 */
void verified_gc_init(size_t heap_size);

/**
 * Trigger a GC cycle
 * Can be called from any thread.
 */
void verified_gc_collect(void);

/**
 * Shutdown the verified GC
 * Called at program exit.
 */
void verified_gc_shutdown(void);

/* =========================================================================
 * OCaml Runtime Hooks
 * ========================================================================= */

/**
 * Hook into caml_modify
 * 
 * Original:
 *   void caml_modify(value *fp, value val)
 *
 * Modified to include write barrier:
 *   void caml_modify(value *fp, value val) {
 *     verified_gc_write_barrier((value)fp, val);  // Before write
 *     *fp = val;                                   // Actual write
 *   }
 */

/**
 * Hook into caml_initialize
 * 
 * Original:
 *   void caml_initialize(value *fp, value val)
 *
 * Modified to include write barrier:
 *   void caml_initialize(value *fp, value val) {
 *     verified_gc_write_barrier((value)fp, val);  // Before write
 *     *fp = val;                                   // Actual write
 *   }
 */

/**
 * Hook into CAMLlocal/CAMLreturn macros
 *
 * CAMLlocal(var):
 *   value var = 0;
 *   verified_gc_push_root(&var);
 *
 * CAMLreturn(val):
 *   verified_gc_pop_root();
 *   return val;
 */

/* =========================================================================
 * GC Statistics
 * ========================================================================= */

typedef struct {
    uint64_t gc_cycles;
    uint64_t total_allocated;
    uint64_t total_reclaimed;
    uint64_t max_pause_ns;
    uint64_t avg_pause_ns;
} gc_stats_t;

/**
 * Get current GC statistics
 */
gc_stats_t verified_gc_get_stats(void);

/* =========================================================================
 * Debugging and Verification
 * ========================================================================= */

/**
 * Check tri-color invariant (debug mode only)
 * Returns true if invariant holds, false if violated.
 */
bool verified_gc_check_tri_color_inv(void);

/**
 * Dump GC state to stderr (debug mode only)
 */
void verified_gc_dump_state(void);

#endif /* VERIFIED_GC_RUNTIME_INTEGRATION_H */
