/// ---------------------------------------------------------------------------
/// GC.Spec.RememberedSet - Pure spec for the intergenerational ref table
/// ---------------------------------------------------------------------------
///
/// Stage 2 of the generational extension. Models the table that records
/// major-heap field locations holding pointers into the minor heap. Used
/// by the minor collector as a seed of roots, and by the write barrier
/// (Stage 2 sibling module `GC.Spec.WriteBarrier`) as an output buffer.
///
/// Stage 2 scope here is the **data-structure** layer only: the logical
/// `ref_table = seq ref_loc` type, the operations on it (empty, snoc,
/// length, index, clear), and a few decidable predicates. The
/// "is this address in the minor heap?" decision and the write barrier
/// itself are in `GC.Spec.WriteBarrier`.

module GC.Spec.RememberedSet

open FStar.Seq

module U64 = FStar.UInt64

open GC.Spec.Base

/// ---------------------------------------------------------------------------
/// Entry type
/// ---------------------------------------------------------------------------

/// A remembered-set entry: a `(holder, field_idx)` pair. `holder` is the
/// address of a major-heap object whose field at `field_idx` was
/// observed (by the write barrier) to point into the minor heap.
///
/// `field_idx` is the 1-based field index used throughout the rest of
/// the spec (`field[0]` is at byte offset 0 from the object address;
/// the header lives 8 bytes earlier). We keep it as a `U64.t` so that
/// the Pulse implementation can store it in a plain `V.vec U64.t`
/// alongside the holder address, without needing custom-typed vectors.
noeq
type ref_loc = {
  holder    : U64.t;
  field_idx : U64.t;
}

/// ---------------------------------------------------------------------------
/// Logical ref table
/// ---------------------------------------------------------------------------

/// The remembered set as a finite sequence of entries. Duplicates are
/// tolerated by the minor collector (the `is_forwarded` short-circuit
/// in `oldify_one_spec` discards repeat visits — see
/// `docs/gen-gc-design/04-invariants-and-termination.md`, invariant 6).
let ref_table = Seq.seq ref_loc

/// Empty ref table.
let empty_ref_table : ref_table = Seq.empty #ref_loc

/// Append a new entry at the tail.
let add_ref (rt: ref_table) (e: ref_loc) : ref_table = Seq.snoc rt e

/// Index the ref table.
let get_ref (rt: ref_table) (i: nat{i < Seq.length rt}) : ref_loc =
  Seq.index rt i

/// Reset to empty (used after a minor collect drains the table).
let clear_ref_table (_rt: ref_table) : ref_table = empty_ref_table

/// ---------------------------------------------------------------------------
/// Sizing
/// ---------------------------------------------------------------------------
///
/// The maximum number of entries. Sized at `minor_size / (2 * mword)`
/// to upper-bound the count of distinct promotable minor objects (the
/// smallest promotable object occupies 2 words: one header + one
/// field). Duplicates can push the entry count higher in pathological
/// cases; on overflow `gen_modify` triggers an eager minor collect
/// (see `docs/gen-gc-design/02-remembered-set-scope.md`).

open GC.Spec.MinorHeap

let max_refs : pos =
  // minor_size is bounded; the division is well-defined.
  let m = minor_size / (2 * U64.v mword) in
  if m < 1 then 1 else m

/// The ref table is full when it has reached its fixed capacity.
let is_full_ref_table (rt: ref_table) : bool =
  Seq.length rt >= max_refs

/// ---------------------------------------------------------------------------
/// Membership and structural lemmas
/// ---------------------------------------------------------------------------

/// `Seq.snoc` preserves all existing entries and appends one at the tail.
let add_ref_length (rt: ref_table) (e: ref_loc)
  : Lemma (Seq.length (add_ref rt e) == Seq.length rt + 1)
  = ()

let add_ref_old (rt: ref_table) (e: ref_loc) (i: nat{i < Seq.length rt})
  : Lemma (get_ref (add_ref rt e) i == get_ref rt i)
  = Seq.lemma_index_app1 rt (Seq.create 1 e) i

let add_ref_new (rt: ref_table) (e: ref_loc)
  : Lemma (get_ref (add_ref rt e) (Seq.length rt) == e)
  = Seq.lemma_index_app2 rt (Seq.create 1 e) (Seq.length rt)

let clear_ref_table_length (rt: ref_table)
  : Lemma (Seq.length (clear_ref_table rt) == 0)
  = ()
