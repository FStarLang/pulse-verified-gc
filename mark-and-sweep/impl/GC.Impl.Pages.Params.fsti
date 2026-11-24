/// ---------------------------------------------------------------------------
/// GC.Impl.Pages.Params - the page allocator's parameters, as machine values
/// ---------------------------------------------------------------------------
///
/// `GC.Spec.Pages.Params` keeps the page size and the class table abstract,
/// so that no proof depends on their values.  The Pulse page allocator needs
/// them as constants it can compute with; this interface gives each one with
/// its value tied to the specification's, and nothing more.  Only the
/// implementation of this module sees the values (`friend`).

module GC.Impl.Pages.Params

open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout

module U64 = FStar.UInt64

/// Words per page.
inline_for_extraction
val page_wsize_u64 : n: U64.t{U64.v n == page_wsize}

/// The number of classes.
inline_for_extraction
val n_cls_u64 : n: U64.t{U64.v n == n_cls}

/// The slot size of class `c`, in words.
val cls_u64 (c: U64.t{U64.v c < n_cls}) : r: U64.t{U64.v r == cls (U64.v c)}

/// The slots of a page of class `c`.
val n_slots_u64 (c: U64.t{U64.v c < n_cls}) : r: U64.t{U64.v r == n_slots (U64.v c)}

/// The class of a block of `w` words, header included: OCaml 5's
/// `sizeclass_wsize` lookup.
val class_u64 (w: U64.t{1 <= U64.v w /\ U64.v w <= small_max}) : r: U64.t{U64.v r == class_of (U64.v w)}
