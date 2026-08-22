/// ---------------------------------------------------------------------------
/// GC.Gen.HeapExtensional — Heap byte-level extensionality via word reads
/// ---------------------------------------------------------------------------
///
/// Proves: if two heaps agree on every aligned word read, they are equal.
/// Strategy: show combine_bytes is injective by extracting individual bytes.

module GC.Gen.HeapExtensional

open FStar.Seq
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module UInt = FStar.UInt
module Math = FStar.Math.Lemmas

open GC.Spec.Base
open GC.Spec.Heap

/// ---------------------------------------------------------------------------
/// combine_bytes byte extraction lemmas
/// ---------------------------------------------------------------------------

/// Arithmetic characterization: combine_bytes is the little-endian sum
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
private let shift_no_overflow (b: U8.t) (s: nat{s < 64 /\ s % 8 == 0})
  : Lemma (U8.v b * pow2 s < pow2 64)
  = Math.pow2_plus 8 s; Math.pow2_le_compat 64 (8 + s)

private let combine_bytes_value (b0 b1 b2 b3 b4 b5 b6 b7: U8.t)
  : Lemma (U64.v (combine_bytes b0 b1 b2 b3 b4 b5 b6 b7) ==
           U8.v b0 + U8.v b1 * pow2 8 + U8.v b2 * pow2 16 + U8.v b3 * pow2 24 +
           U8.v b4 * pow2 32 + U8.v b5 * pow2 40 + U8.v b6 * pow2 48 + U8.v b7 * pow2 56)
  = shift_no_overflow b1 8; shift_no_overflow b2 16; shift_no_overflow b3 24;
    shift_no_overflow b4 32; shift_no_overflow b5 40; shift_no_overflow b6 48;
    shift_no_overflow b7 56;
    let v0 : UInt.uint_t 64 = U8.v b0 in
    let v1 : UInt.uint_t 64 = U8.v b1 * pow2 8 in
    let v2 : UInt.uint_t 64 = U8.v b2 * pow2 16 in
    let v3 : UInt.uint_t 64 = U8.v b3 * pow2 24 in
    let v4 : UInt.uint_t 64 = U8.v b4 * pow2 32 in
    let v5 : UInt.uint_t 64 = U8.v b5 * pow2 40 in
    let v6 : UInt.uint_t 64 = U8.v b6 * pow2 48 in
    let v7 : UInt.uint_t 64 = U8.v b7 * pow2 56 in
    Math.small_mod v1 (pow2 64); Math.small_mod v2 (pow2 64);
    Math.small_mod v3 (pow2 64); Math.small_mod v4 (pow2 64);
    Math.small_mod v5 (pow2 64); Math.small_mod v6 (pow2 64);
    Math.small_mod v7 (pow2 64);
    UInt.logor_commutative #64 v0 v1; UInt.logor_disjoint #64 v1 v0 8;
    assert_norm (255 * pow2 8 + pow2 8 == pow2 16);
    UInt.logor_commutative #64 (v0+v1) v2; UInt.logor_disjoint #64 v2 (v0+v1) 16;
    assert_norm (255 * pow2 16 + pow2 16 == pow2 24);
    UInt.logor_commutative #64 (v0+v1+v2) v3; UInt.logor_disjoint #64 v3 (v0+v1+v2) 24;
    assert_norm (255 * pow2 24 + pow2 24 == pow2 32);
    UInt.logor_commutative #64 (v0+v1+v2+v3) v4; UInt.logor_disjoint #64 v4 (v0+v1+v2+v3) 32;
    assert_norm (255 * pow2 32 + pow2 32 == pow2 40);
    UInt.logor_commutative #64 (v0+v1+v2+v3+v4) v5; UInt.logor_disjoint #64 v5 (v0+v1+v2+v3+v4) 40;
    assert_norm (255 * pow2 40 + pow2 40 == pow2 48);
    UInt.logor_commutative #64 (v0+v1+v2+v3+v4+v5) v6; UInt.logor_disjoint #64 v6 (v0+v1+v2+v3+v4+v5) 48;
    assert_norm (255 * pow2 48 + pow2 48 == pow2 56);
    UInt.logor_commutative #64 (v0+v1+v2+v3+v4+v5+v6) v7; UInt.logor_disjoint #64 v7 (v0+v1+v2+v3+v4+v5+v6) 56
#pop-options

private let pow2_factor_norms () : Lemma (
  pow2 16 == pow2 8 * pow2 8 /\
  pow2 24 == pow2 8 * pow2 16 /\
  pow2 32 == pow2 8 * pow2 24 /\
  pow2 40 == pow2 8 * pow2 32 /\
  pow2 48 == pow2 8 * pow2 40 /\
  pow2 56 == pow2 8 * pow2 48)
  = assert_norm (pow2 16 == pow2 8 * pow2 8);
    assert_norm (pow2 24 == pow2 8 * pow2 16);
    assert_norm (pow2 32 == pow2 8 * pow2 24);
    assert_norm (pow2 40 == pow2 8 * pow2 32);
    assert_norm (pow2 48 == pow2 8 * pow2 40);
    assert_norm (pow2 56 == pow2 8 * pow2 48)

/// General digit extraction: if sum = low + high*divisor with low < divisor,
/// and high = bk + rest*256 with bk < 256, then (sum/divisor) % 256 = bk.
private let extract_digit (sum low high bk rest divisor: nat)
  : Lemma
    (requires sum == low + high * divisor /\ low < divisor /\ divisor > 0 /\
              high == bk + rest * pow2 8 /\ bk < pow2 8)
    (ensures (sum / divisor) % pow2 8 == bk)
  = Math.lemma_div_plus low high divisor;
    Math.small_div low divisor;
    Math.lemma_mod_plus bk rest (pow2 8);
    Math.small_mod bk (pow2 8)

/// Byte extraction: decomposing combine_bytes recovers each original byte
#push-options "--z3rlimit 25 --fuel 0 --ifuel 0"
private let combine_byte0 (b0 b1 b2 b3 b4 b5 b6 b7: U8.t)
  : Lemma (uint64_to_uint8 (combine_bytes b0 b1 b2 b3 b4 b5 b6 b7) == b0)
  = combine_bytes_value b0 b1 b2 b3 b4 b5 b6 b7; pow2_factor_norms ();
    let sum = U64.v (combine_bytes b0 b1 b2 b3 b4 b5 b6 b7) in
    let high = U8.v b1 + U8.v b2*pow2 8 + U8.v b3*pow2 16 + U8.v b4*pow2 24 + U8.v b5*pow2 32 + U8.v b6*pow2 40 + U8.v b7*pow2 48 in
    Math.lemma_mod_plus (U8.v b0) high (pow2 8);
    Math.small_mod (U8.v b0) (pow2 8)

private let combine_byte1 (b0 b1 b2 b3 b4 b5 b6 b7: U8.t)
  : Lemma (uint64_to_uint8 (U64.shift_right (combine_bytes b0 b1 b2 b3 b4 b5 b6 b7) 8ul) == b1)
  = combine_bytes_value b0 b1 b2 b3 b4 b5 b6 b7; pow2_factor_norms ();
    let sum = U64.v (combine_bytes b0 b1 b2 b3 b4 b5 b6 b7) in
    let high = U8.v b1 + U8.v b2*pow2 8 + U8.v b3*pow2 16 + U8.v b4*pow2 24 + U8.v b5*pow2 32 + U8.v b6*pow2 40 + U8.v b7*pow2 48 in
    extract_digit sum (U8.v b0) high (U8.v b1) (U8.v b2 + U8.v b3*pow2 8 + U8.v b4*pow2 16 + U8.v b5*pow2 24 + U8.v b6*pow2 32 + U8.v b7*pow2 40) (pow2 8)

private let combine_byte2 (b0 b1 b2 b3 b4 b5 b6 b7: U8.t)
  : Lemma (uint64_to_uint8 (U64.shift_right (combine_bytes b0 b1 b2 b3 b4 b5 b6 b7) 16ul) == b2)
  = combine_bytes_value b0 b1 b2 b3 b4 b5 b6 b7; pow2_factor_norms ();
    let sum = U64.v (combine_bytes b0 b1 b2 b3 b4 b5 b6 b7) in
    let low = U8.v b0 + U8.v b1*pow2 8 in
    let high = U8.v b2 + U8.v b3*pow2 8 + U8.v b4*pow2 16 + U8.v b5*pow2 24 + U8.v b6*pow2 32 + U8.v b7*pow2 40 in
    extract_digit sum low high (U8.v b2) (U8.v b3 + U8.v b4*pow2 8 + U8.v b5*pow2 16 + U8.v b6*pow2 24 + U8.v b7*pow2 32) (pow2 16)

private let combine_byte3 (b0 b1 b2 b3 b4 b5 b6 b7: U8.t)
  : Lemma (uint64_to_uint8 (U64.shift_right (combine_bytes b0 b1 b2 b3 b4 b5 b6 b7) 24ul) == b3)
  = combine_bytes_value b0 b1 b2 b3 b4 b5 b6 b7; pow2_factor_norms ();
    let sum = U64.v (combine_bytes b0 b1 b2 b3 b4 b5 b6 b7) in
    let low = U8.v b0 + U8.v b1*pow2 8 + U8.v b2*pow2 16 in
    let high = U8.v b3 + U8.v b4*pow2 8 + U8.v b5*pow2 16 + U8.v b6*pow2 24 + U8.v b7*pow2 32 in
    extract_digit sum low high (U8.v b3) (U8.v b4 + U8.v b5*pow2 8 + U8.v b6*pow2 16 + U8.v b7*pow2 24) (pow2 24)

private let combine_byte4 (b0 b1 b2 b3 b4 b5 b6 b7: U8.t)
  : Lemma (uint64_to_uint8 (U64.shift_right (combine_bytes b0 b1 b2 b3 b4 b5 b6 b7) 32ul) == b4)
  = combine_bytes_value b0 b1 b2 b3 b4 b5 b6 b7; pow2_factor_norms ();
    let sum = U64.v (combine_bytes b0 b1 b2 b3 b4 b5 b6 b7) in
    let low = U8.v b0 + U8.v b1*pow2 8 + U8.v b2*pow2 16 + U8.v b3*pow2 24 in
    let high = U8.v b4 + U8.v b5*pow2 8 + U8.v b6*pow2 16 + U8.v b7*pow2 24 in
    extract_digit sum low high (U8.v b4) (U8.v b5 + U8.v b6*pow2 8 + U8.v b7*pow2 16) (pow2 32)

private let combine_byte5 (b0 b1 b2 b3 b4 b5 b6 b7: U8.t)
  : Lemma (uint64_to_uint8 (U64.shift_right (combine_bytes b0 b1 b2 b3 b4 b5 b6 b7) 40ul) == b5)
  = combine_bytes_value b0 b1 b2 b3 b4 b5 b6 b7; pow2_factor_norms ();
    let sum = U64.v (combine_bytes b0 b1 b2 b3 b4 b5 b6 b7) in
    let low = U8.v b0 + U8.v b1*pow2 8 + U8.v b2*pow2 16 + U8.v b3*pow2 24 + U8.v b4*pow2 32 in
    let high = U8.v b5 + U8.v b6*pow2 8 + U8.v b7*pow2 16 in
    extract_digit sum low high (U8.v b5) (U8.v b6 + U8.v b7*pow2 8) (pow2 40)

private let combine_byte6 (b0 b1 b2 b3 b4 b5 b6 b7: U8.t)
  : Lemma (uint64_to_uint8 (U64.shift_right (combine_bytes b0 b1 b2 b3 b4 b5 b6 b7) 48ul) == b6)
  = combine_bytes_value b0 b1 b2 b3 b4 b5 b6 b7; pow2_factor_norms ();
    let sum = U64.v (combine_bytes b0 b1 b2 b3 b4 b5 b6 b7) in
    let low = U8.v b0 + U8.v b1*pow2 8 + U8.v b2*pow2 16 + U8.v b3*pow2 24 + U8.v b4*pow2 32 + U8.v b5*pow2 40 in
    let high = U8.v b6 + U8.v b7*pow2 8 in
    extract_digit sum low high (U8.v b6) (U8.v b7) (pow2 48)

private let combine_byte7 (b0 b1 b2 b3 b4 b5 b6 b7: U8.t)
  : Lemma (uint64_to_uint8 (U64.shift_right (combine_bytes b0 b1 b2 b3 b4 b5 b6 b7) 56ul) == b7)
  = combine_bytes_value b0 b1 b2 b3 b4 b5 b6 b7; pow2_factor_norms ();
    let sum = U64.v (combine_bytes b0 b1 b2 b3 b4 b5 b6 b7) in
    let low = U8.v b0 + U8.v b1*pow2 8 + U8.v b2*pow2 16 + U8.v b3*pow2 24 + U8.v b4*pow2 32 + U8.v b5*pow2 40 + U8.v b6*pow2 48 in
    Math.lemma_div_plus low (U8.v b7) (pow2 56);
    Math.small_div low (pow2 56);
    Math.small_mod (U8.v b7) (pow2 8)
#pop-options

/// ---------------------------------------------------------------------------
/// Main lemma: heap extensionality from word reads
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 12 --fuel 0 --ifuel 0"
private let aligned_lt_heap_size (i: nat{i < heap_size})
  : Lemma ((i / 8) * 8 + 7 < heap_size)
  = let a = (i / 8) * 8 in
    assert (a <= i);
    assert (a % 8 == 0);
    assert (heap_size % 8 == 0);
    assert (a < heap_size)

/// Build the `hp_addr` for a word-aligned in-bounds offset.
///
/// Query splitting checks the `hp_addr` refinement in the caller's full
/// context, where `U64.v (U64.uint_to_t a) % 8 == 0` is expensive; proving it
/// once here keeps the caller's goals trivial.
private let mk_hp_addr (a: nat{a < heap_size /\ a % 8 == 0}) : (r: hp_addr{U64.v r == a}) =
  assert (a < pow2 64);
  U64.uint_to_t a

/// Euclidean division at the word width, discharged in an empty context.
private let div_mod_8 (i: nat) : Lemma ((i / 8) * 8 + i % 8 == i)
  = Math.lemma_div_mod i 8

/// All eight bytes of an aligned word agree whenever the word reads agree.
///
/// Factored out of `heap_read_word_ext` so that the eight-way case analysis on
/// the byte offset runs in a minimal context, rather than under the outer
/// universally quantified extensionality hypothesis.
private let bytes_eq_of_word_eq (h1 h2: heap) (a: nat)
  : Lemma
    (requires a % 8 == 0 /\ a + 7 < heap_size /\
              read_word h1 (mk_hp_addr a) == read_word h2 (mk_hp_addr a))
    (ensures Seq.index h1 a       == Seq.index h2 a       /\
             Seq.index h1 (a + 1) == Seq.index h2 (a + 1) /\
             Seq.index h1 (a + 2) == Seq.index h2 (a + 2) /\
             Seq.index h1 (a + 3) == Seq.index h2 (a + 3) /\
             Seq.index h1 (a + 4) == Seq.index h2 (a + 4) /\
             Seq.index h1 (a + 5) == Seq.index h2 (a + 5) /\
             Seq.index h1 (a + 6) == Seq.index h2 (a + 6) /\
             Seq.index h1 (a + 7) == Seq.index h2 (a + 7))
  = let ha = mk_hp_addr a in
    read_word_spec h1 ha;
    read_word_spec h2 ha;
    let b10 = Seq.index h1 a in let b11 = Seq.index h1 (a+1) in
    let b12 = Seq.index h1 (a+2) in let b13 = Seq.index h1 (a+3) in
    let b14 = Seq.index h1 (a+4) in let b15 = Seq.index h1 (a+5) in
    let b16 = Seq.index h1 (a+6) in let b17 = Seq.index h1 (a+7) in
    let b20 = Seq.index h2 a in let b21 = Seq.index h2 (a+1) in
    let b22 = Seq.index h2 (a+2) in let b23 = Seq.index h2 (a+3) in
    let b24 = Seq.index h2 (a+4) in let b25 = Seq.index h2 (a+5) in
    let b26 = Seq.index h2 (a+6) in let b27 = Seq.index h2 (a+7) in
    combine_byte0 b10 b11 b12 b13 b14 b15 b16 b17;
    combine_byte0 b20 b21 b22 b23 b24 b25 b26 b27;
    combine_byte1 b10 b11 b12 b13 b14 b15 b16 b17;
    combine_byte1 b20 b21 b22 b23 b24 b25 b26 b27;
    combine_byte2 b10 b11 b12 b13 b14 b15 b16 b17;
    combine_byte2 b20 b21 b22 b23 b24 b25 b26 b27;
    combine_byte3 b10 b11 b12 b13 b14 b15 b16 b17;
    combine_byte3 b20 b21 b22 b23 b24 b25 b26 b27;
    combine_byte4 b10 b11 b12 b13 b14 b15 b16 b17;
    combine_byte4 b20 b21 b22 b23 b24 b25 b26 b27;
    combine_byte5 b10 b11 b12 b13 b14 b15 b16 b17;
    combine_byte5 b20 b21 b22 b23 b24 b25 b26 b27;
    combine_byte6 b10 b11 b12 b13 b14 b15 b16 b17;
    combine_byte6 b20 b21 b22 b23 b24 b25 b26 b27;
    combine_byte7 b10 b11 b12 b13 b14 b15 b16 b17;
    combine_byte7 b20 b21 b22 b23 b24 b25 b26 b27;
    assert (b10 == b20 /\ b11 == b21 /\ b12 == b22 /\ b13 == b23 /\
            b14 == b24 /\ b15 == b25 /\ b16 == b26 /\ b17 == b27)

let heap_read_word_ext (h1 h2: heap)
  : Lemma
    (requires (forall (a: nat).
       a < heap_size /\ a % 8 == 0 ==>
       read_word h1 (U64.uint_to_t a) == read_word h2 (U64.uint_to_t a)))
    (ensures h1 == h2)
  = let aux (i: nat{i < heap_size}) : Lemma (Seq.index h1 i == Seq.index h2 i) =
      let a = (i / 8) * 8 in
      aligned_lt_heap_size i;
      bytes_eq_of_word_eq h1 h2 a;
      div_mod_8 i;
      let r = i % 8 in
      assert (i == a + r);
      assert (r == 0 \/ r == 1 \/ r == 2 \/ r == 3 \/
              r == 4 \/ r == 5 \/ r == 6 \/ r == 7)
    in
    FStar.Classical.forall_intro aux;
    Seq.lemma_eq_intro h1 h2
#pop-options
