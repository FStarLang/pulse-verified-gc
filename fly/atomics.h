/**
 * atomics.h - C11 Atomics Wrapper for Pulse GC
 *
 * This header provides C11 atomic operations that map to Pulse's
 * stt_atomic primitives. Used by KaRaMeL-extracted code.
 */

#ifndef PULSE_GC_ATOMICS_H
#define PULSE_GC_ATOMICS_H

#include <stdint.h>
#include <stdatomic.h>
#include <stdbool.h>

/* =========================================================================
 * Type Definitions
 * ========================================================================= */

/* Heap address type (64-bit) */
typedef uint64_t hp_addr;

/* Atomic color type - stored in object headers */
typedef _Atomic uint64_t atomic_color_t;

/* Object color constants */
#define GC_COLOR_BLUE  0ULL  /* Free/reclaimed */
#define GC_COLOR_WHITE 1ULL  /* Unvisited */
#define GC_COLOR_GRAY  2ULL  /* To be scanned */
#define GC_COLOR_BLACK 3ULL  /* Scanned */

/* Header layout constants */
#define COLOR_SHIFT 8ULL
#define COLOR_MASK  0x300ULL
#define TAG_MASK    0xFFULL
#define WOSIZE_SHIFT 10ULL

/* =========================================================================
 * Atomic Color Operations
 * ========================================================================= */

/**
 * Read object color atomically
 *
 * Maps to Pulse: read_color_atomic
 * Memory order: memory_order_acquire
 */
static inline uint64_t gc_read_color(volatile uint64_t *header) {
    uint64_t hdr = atomic_load_explicit((atomic_color_t*)header, 
                                        memory_order_acquire);
    return (hdr & COLOR_MASK) >> COLOR_SHIFT;
}

/**
 * CAS object color atomically
 *
 * Maps to Pulse: cas_color_atomic
 * Memory order: memory_order_acq_rel on success, memory_order_acquire on failure
 *
 * Returns: true if CAS succeeded, false otherwise
 */
static inline bool gc_cas_color(volatile uint64_t *header,
                                 uint64_t expected_color,
                                 uint64_t new_color) {
    uint64_t old_hdr = atomic_load_explicit((atomic_color_t*)header,
                                            memory_order_relaxed);
    uint64_t current_color = (old_hdr & COLOR_MASK) >> COLOR_SHIFT;
    
    if (current_color != expected_color) {
        return false;
    }
    
    /* Compute new header with updated color */
    uint64_t new_hdr = (old_hdr & ~COLOR_MASK) | (new_color << COLOR_SHIFT);
    
    return atomic_compare_exchange_weak_explicit(
        (atomic_color_t*)header,
        &old_hdr,
        new_hdr,
        memory_order_acq_rel,
        memory_order_acquire
    );
}

/**
 * Write object color atomically
 *
 * Maps to Pulse: write_color (when available)
 * Memory order: memory_order_release
 */
static inline void gc_write_color(volatile uint64_t *header, uint64_t color) {
    uint64_t old_hdr = atomic_load_explicit((atomic_color_t*)header,
                                            memory_order_relaxed);
    uint64_t new_hdr = (old_hdr & ~COLOR_MASK) | (color << COLOR_SHIFT);
    atomic_store_explicit((atomic_color_t*)header, new_hdr, memory_order_release);
}

/* =========================================================================
 * Header Field Access
 * ========================================================================= */

/**
 * Get word size from header
 */
static inline uint64_t gc_get_wosize(uint64_t header) {
    return header >> WOSIZE_SHIFT;
}

/**
 * Get tag from header
 */
static inline uint64_t gc_get_tag(uint64_t header) {
    return header & TAG_MASK;
}

/**
 * Make a new header with specified color
 */
static inline uint64_t gc_make_header(uint64_t wosize, uint64_t color, uint64_t tag) {
    return (wosize << WOSIZE_SHIFT) | (color << COLOR_SHIFT) | tag;
}

/**
 * Update header with new color
 */
static inline uint64_t gc_color_header(uint64_t header, uint64_t color) {
    return (header & ~COLOR_MASK) | (color << COLOR_SHIFT);
}

/* =========================================================================
 * Memory Barriers
 * ========================================================================= */

/**
 * Full memory fence
 */
static inline void gc_memory_fence(void) {
    atomic_thread_fence(memory_order_seq_cst);
}

/**
 * Acquire fence (for reading)
 */
static inline void gc_acquire_fence(void) {
    atomic_thread_fence(memory_order_acquire);
}

/**
 * Release fence (for writing)
 */
static inline void gc_release_fence(void) {
    atomic_thread_fence(memory_order_release);
}

/* =========================================================================
 * Atomic Flag Operations (for barriers)
 * ========================================================================= */

typedef _Atomic bool atomic_flag_t;

/**
 * Set atomic flag
 */
static inline void gc_set_flag(atomic_flag_t *flag) {
    atomic_store_explicit(flag, true, memory_order_release);
}

/**
 * Clear atomic flag
 */
static inline void gc_clear_flag(atomic_flag_t *flag) {
    atomic_store_explicit(flag, false, memory_order_release);
}

/**
 * Read atomic flag
 */
static inline bool gc_read_flag(atomic_flag_t *flag) {
    return atomic_load_explicit(flag, memory_order_acquire);
}

/**
 * Wait for flag to become expected value (spin-wait)
 */
static inline void gc_wait_flag(atomic_flag_t *flag, bool expected) {
    while (atomic_load_explicit(flag, memory_order_acquire) != expected) {
        /* Busy wait - could add pause instruction for better CPU efficiency */
        #if defined(__x86_64__) || defined(__i386__)
        __asm__ __volatile__("pause" ::: "memory");
        #elif defined(__aarch64__)
        __asm__ __volatile__("yield" ::: "memory");
        #endif
    }
}

/* =========================================================================
 * Atomic Counter Operations (for statistics)
 * ========================================================================= */

typedef _Atomic uint64_t atomic_counter_t;

/**
 * Atomic increment
 */
static inline uint64_t gc_atomic_inc(atomic_counter_t *counter) {
    return atomic_fetch_add_explicit(counter, 1, memory_order_relaxed);
}

/**
 * Atomic add
 */
static inline uint64_t gc_atomic_add(atomic_counter_t *counter, uint64_t value) {
    return atomic_fetch_add_explicit(counter, value, memory_order_relaxed);
}

/**
 * Atomic load counter
 */
static inline uint64_t gc_atomic_load(atomic_counter_t *counter) {
    return atomic_load_explicit(counter, memory_order_relaxed);
}

#endif /* PULSE_GC_ATOMICS_H */
