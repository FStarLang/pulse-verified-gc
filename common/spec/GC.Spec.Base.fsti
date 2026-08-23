/// ---------------------------------------------------------------------------
/// GC.Spec.Base - Foundational types for verified GC
/// ---------------------------------------------------------------------------
///
/// This module provides the core types used throughout the GC specification:
/// - Machine word constants
/// - Heap type (byte-addressable sequence)
/// - Address types (word-aligned pointers)

module GC.Spec.Base

open FStar.Seq

module U64 = FStar.UInt64
module U8 = FStar.UInt8

/// ---------------------------------------------------------------------------
/// Machine Constants
/// ---------------------------------------------------------------------------

/// Machine word size in bytes (8 for 64-bit)
inline_for_extraction
let mword : m:U64.t{U64.v m == 8 /\ U64.v m <> 0} = 8UL

/// Heap size in bytes (abstract — proofs work for any word-aligned size below pow2 57)
/// The strict pow2 57 bound ensures accumulated blue run words fit in pow2 54 - 1.
/// Combined with mword=8, h_addr + (1+wosize)*mword doesn't overflow U64.
/// Minimum 16 bytes (header + one field) to hold at least one object.
val heap_size : n:pos{n % U64.v mword == 0 /\ n >= 16 /\ n < pow2 57 /\ n < pow2 64}

/// The heap size measured in words -- the standard fuel bound for free-list
/// traversals.  Naming it keeps the (trivial) nat-ness obligation
/// `heap_size / mword >= 0`, which requires unfolding `mword`, out of the
/// very large proof contexts where the solver diverges on it.
let heap_words : nat = heap_size / U64.v mword

/// Heap size as U64 — left as an extern so the runtime can configure it.
val heap_size_u64 : n:U64.t{U64.v n == heap_size}

/// ---------------------------------------------------------------------------
/// Heap Type
/// ---------------------------------------------------------------------------

/// Heap is a byte-addressable array of fixed size
let heap = h:seq U8.t{Seq.length h == heap_size}

/// ---------------------------------------------------------------------------
/// Address Types
/// ---------------------------------------------------------------------------

/// Word-aligned address within heap bounds
let hp_addr = a:U64.t{
  U64.v a >= 0 /\ 
  U64.v a < heap_size /\ 
  U64.v a % U64.v mword == 0
}
/// Base address of the heap (abstract — instantiated at deployment).
/// Must have room for at least one object header after it.
val zero_addr : a:hp_addr{U64.v a + U64.v mword < heap_size}

/// Configuration lemma: zero_addr >= 2048 (the minor heap size constant).
/// This ensures major-heap addresses cannot be confused with minor offsets.
val zero_addr_above_2048 (_:unit) : Lemma (U64.v zero_addr >= 2048)

/// Object address: hp_addr with room for header before it (>= 8)
/// Used for all operations that access object headers via hd_address
type obj_addr = a:hp_addr{U64.v a >= U64.v mword}
/// ---------------------------------------------------------------------------
/// Address Predicates
/// ---------------------------------------------------------------------------

/// Check if a value is a valid heap pointer address
val is_hp_addr (a: U64.t) : bool

/// Check if address has room for header
val is_val_addr (a: U64.t) : bool

/// Specification of is_val_addr (unfolds its definition for SMT)
val is_val_addr_spec (a: U64.t)
  : Lemma (ensures is_val_addr a <==>
                   (U64.v a >= U64.v mword /\ U64.v a < heap_size /\ U64.v a % U64.v mword == 0))
    [SMTPat (is_val_addr a)]

/// ---------------------------------------------------------------------------
/// Address Arithmetic Lemmas
/// ---------------------------------------------------------------------------
/// ---------------------------------------------------------------------------
/// Utility Types
/// ---------------------------------------------------------------------------
/// Build an `hp_addr` from a raw byte offset.  The well-typedness obligations
/// (`UInt.size a 64` and `U64.v (uint_to_t a) % U64.v mword == 0`) are trivial,
/// but under the very large contexts of the collector proofs the solver
/// diverges on them.  Discharging them once, here, in an empty context, keeps
/// them out of those contexts.
val mk_hp_addr (a: nat{a < heap_size /\ a % U64.v mword == 0})
  : (r: hp_addr{U64.v r == a /\ r == U64.uint_to_t a})

/// `base + k * mword` stays word-aligned.  Like `mk_hp_addr`, this trivial
/// modular-arithmetic step diverges under large collector contexts, so it is
/// discharged once here.
val aligned_plus_mul8 (base k: nat)
  : Lemma (requires base % U64.v mword == 0)
          (ensures (base + k * 8) % U64.v mword == 0)
