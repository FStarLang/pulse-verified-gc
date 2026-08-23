module GC.Lib.Address

/// Address Arithmetic Lemmas for Field Access
/// 
/// These lemmas prove separation properties between field addresses and headers.
/// All reasoning is done on U64.v values (nat), which Z3 handles efficiently.
/// The actual types remain U64.t for compatibility with existing code.

open FStar.UInt64
module U64 = FStar.UInt64

open GC.Spec.Base

/// ---------------------------------------------------------------------------
/// Field Address Computation
/// ---------------------------------------------------------------------------

/// Type alias for valid field index (fields start at index 1, not 0)
type field_index = i:U64.t{U64.v i >= 1}

/// Precondition: field address computation won't overflow
let field_addr_safe (h: U64.t) (i: field_index) : prop =
  U64.v h + U64.v mword * U64.v i < pow2 64

/// Compute field address: header + mword * index
let field_addr (h: U64.t) (i: field_index) : Pure U64.t
  (requires field_addr_safe h i)
  (ensures fun r -> U64.v r = U64.v h + U64.v mword * U64.v i)
  = U64.add h (U64.mul mword i)

/// ---------------------------------------------------------------------------
/// Core Separation Lemmas (reasoning in U64.v domain = nat)
/// ---------------------------------------------------------------------------
/// Same as above but with heap_size bound (implies field_addr_safe)
let field_header_separated_heap (h: U64.t) (i: field_index)
  : Lemma (requires U64.v h + U64.v mword * (U64.v i + 1) <= heap_size)
          (ensures field_addr h i <> h /\
                   U64.v h + U64.v mword <= U64.v (field_addr h i))
  = ()  // heap_size < pow2 64, so field_addr_safe is implied

/// ---------------------------------------------------------------------------
/// Inter-Object Separation Lemmas
/// ---------------------------------------------------------------------------
/// Field doesn't touch other header (matches Fields.fst precondition exactly)
/// h2 can be either before h1's field range or after h1's object
let field_disjoint_from_other2 (h1 h2: U64.t) (i: field_index)
  : Lemma (requires U64.v h1 + U64.v mword * (U64.v i + 1) <= heap_size /\
                    h1 <> h2 /\
                    (U64.v h1 + U64.v mword * (U64.v i + 1) <= U64.v h2 \/
                     U64.v h2 + U64.v mword <= U64.v h1 + U64.v mword * U64.v i))
          (ensures U64.add h1 (U64.mul mword i) <> h2 /\
                   (U64.v (U64.add h1 (U64.mul mword i)) + U64.v mword <= U64.v h2 \/
                    U64.v h2 + U64.v mword <= U64.v (U64.add h1 (U64.mul mword i))))
  = ()  // h2 + 8 <= h1 + 8*i = field_addr, so second disjunct holds

/// ---------------------------------------------------------------------------
/// Alignment Lemmas
/// ---------------------------------------------------------------------------
