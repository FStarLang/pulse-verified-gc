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

/// Field address value equals h + 8*i (for SMT)
let field_addr_value (h: U64.t) (i: field_index)
  : Lemma (requires field_addr_safe h i)
          (ensures U64.v (field_addr h i) = U64.v h + U64.v mword * U64.v i)
  = ()

/// Field is always at least mword (8 bytes) after header
let field_after_header (h: U64.t) (i: field_index)
  : Lemma (requires field_addr_safe h i)
          (ensures U64.v h + U64.v mword <= U64.v (field_addr h i))
  = ()

/// Field address differs from header address
let field_neq_header (h: U64.t) (i: field_index)
  : Lemma (requires field_addr_safe h i)
          (ensures field_addr h i <> h)
  = field_after_header h i

/// Field is separated from header (provides read_write_different precondition)
let field_header_separated (h: U64.t) (i: field_index)
  : Lemma (requires field_addr_safe h i)
          (ensures field_addr h i <> h /\
                   U64.v h + U64.v mword <= U64.v (field_addr h i))
  = field_after_header h i

/// Same as above but with heap_size bound (implies field_addr_safe)
let field_header_separated_heap (h: U64.t) (i: field_index)
  : Lemma (requires U64.v h + U64.v mword * (U64.v i + 1) <= heap_size)
          (ensures field_addr h i <> h /\
                   U64.v h + U64.v mword <= U64.v (field_addr h i))
  = ()  // heap_size < pow2 64, so field_addr_safe is implied

/// ---------------------------------------------------------------------------
/// Inter-Object Separation Lemmas
/// ---------------------------------------------------------------------------

/// Field in h1's body doesn't overlap h2's header (when objects are separated)
let field_other_header_separated (h1 h2: U64.t) (i: field_index) (ws: U64.t)
  : Lemma (requires field_addr_safe h1 i /\
                    U64.v i <= U64.v ws /\
                    h1 <> h2 /\
                    (U64.v h1 + U64.v mword * (U64.v ws + 1) <= U64.v h2 \/
                     U64.v h2 + U64.v mword <= U64.v h1))
          (ensures field_addr h1 i <> h2 /\
                   (U64.v (field_addr h1 i) + U64.v mword <= U64.v h2 \/
                    U64.v h2 + U64.v mword <= U64.v (field_addr h1 i)))
  = ()

/// Simplified version: field doesn't touch other header when addresses are well-separated
let field_disjoint_from_other (h1 h2: U64.t) (i: field_index)
  : Lemma (requires field_addr_safe h1 i /\
                    h1 <> h2 /\
                    (U64.v h1 + U64.v mword * (U64.v i + 1) <= U64.v h2 \/
                     U64.v h2 + U64.v mword <= U64.v h1))
          (ensures field_addr h1 i <> h2 /\
                   (U64.v (field_addr h1 i) + U64.v mword <= U64.v h2 \/
                    U64.v h2 + U64.v mword <= U64.v (field_addr h1 i)))
  = ()

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

/// Word-aligned addresses that differ are at least mword apart
let aligned_separation (a b: U64.t)
  : Lemma (requires U64.v a % U64.v mword = 0 /\ U64.v b % U64.v mword = 0 /\ a <> b)
          (ensures U64.v a + U64.v mword <= U64.v b \/ U64.v b + U64.v mword <= U64.v a)
  = ()

/// Field addresses are word-aligned (since h and mword*i are both aligned)
let field_addr_aligned (h: U64.t) (i: field_index)
  : Lemma (requires U64.v h % U64.v mword = 0 /\ field_addr_safe h i)
          (ensures U64.v (field_addr h i) % U64.v mword = 0)
  = ()

/// Same but with heap_size bound
let field_addr_aligned_heap (h: U64.t) (i: field_index)
  : Lemma (requires U64.v h % U64.v mword = 0 /\ U64.v h + U64.v mword * (U64.v i + 1) <= heap_size)
          (ensures U64.v (U64.add h (U64.mul mword i)) % U64.v mword = 0)
  = ()

/// Aligned separation with heap bound for field address
let field_separated_from_addr (h: U64.t) (i: field_index) (h2: U64.t)
  : Lemma (requires U64.v h % U64.v mword = 0 /\ 
                    U64.v h2 % U64.v mword = 0 /\
                    U64.v h + U64.v mword * (U64.v i + 1) <= heap_size /\
                    U64.add h (U64.mul mword i) <> h2)
          (ensures U64.v (U64.add h (U64.mul mword i)) + U64.v mword <= U64.v h2 \/
                   U64.v h2 + U64.v mword <= U64.v (U64.add h (U64.mul mword i)))
  = field_addr_aligned_heap h i;
    aligned_separation (U64.add h (U64.mul mword i)) h2
