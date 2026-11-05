/// ---------------------------------------------------------------------------
/// GC.Spec.SizeClass - which free list a free block belongs on
/// ---------------------------------------------------------------------------
///
/// The major heap keeps `n_lists = n_small + 1` free lists.  List `w`, for
/// `1 <= w <= n_small`, holds exactly the free blocks of wosize `w`; list 0
/// holds every free block larger than `n_small` words.  Wosize-0 fragments
/// carry no link word and are on no list.
///
/// `n_small` is opaque to the SMT solver, so no proof depends on its value;
/// it is changed here alone, in `n_small_u64` and `n_lists_sz`, which the
/// code uses and `n_small_u64_v` / `n_lists_sz_v` tie to it
/// (docs/allocator-table-and-size-lists.md).

module GC.Spec.SizeClass

module U64 = FStar.UInt64
module SZ = FStar.SizeT

/// The number of exact-fit lists, as the code sees it.
inline_for_extraction noextract
let n_small_u64 : U64.t = 16UL

[@@"opaque_to_smt"]
let n_small : n:nat{n < 64} = U64.v n_small_u64

let n_lists : pos = n_small + 1

/// `n_lists` as an array length.
inline_for_extraction noextract
let n_lists_sz : SZ.t = 17sz

val n_small_u64_v : unit -> Lemma (U64.v n_small_u64 == n_small)

val n_lists_sz_v : unit -> Lemma (SZ.v n_lists_sz == n_lists)

/// The list a free block of wosize `w` belongs on.  Never asked of `w = 0`.
let size_class (w: nat) : nat =
  if 1 <= w && w <= n_small then w else 0

let size_class_lt (w: nat)
  : Lemma (size_class w < n_lists)
  = ()

