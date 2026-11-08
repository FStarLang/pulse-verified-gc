/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Params - the page size and the size-class table
/// ---------------------------------------------------------------------------
///
/// The page allocator (docs/pages-allocator-proof-plan.md) has two
/// parameters: the page size and the table of size classes.  This interface
/// is the only place they are described.  Every other module sees the
/// values as abstract, together with the conditions below, so no proof
/// depends on which values are chosen.
///
/// The conditions, stated once:
///   C1  the smallest class is at least 2 words, so a free slot can hold its
///       header and the free-list link;
///   C2  the classes strictly increase;
///   C3  the largest class, `small_max`, fits in a page;
///   C4  a page is small enough that page arithmetic never overflows;
///   C5  a large block is larger than every exact-fit list of #46
///       (`GC.Spec.SizeClass.n_small`), so the large-object area uses only
///       #46's first-fit list 0.
///
/// Sizes are in words and include the header (whsize), as in OCaml 5's
/// `wsize_sizeclass`.  A block of whsize at most `small_max` is small and
/// goes in a page of its class; a larger block goes to the large-object
/// area.  OCaml 5's waste bound (`max_overhead` in gen_sizeclasses.ml) is
/// not a condition: it concerns memory use, not correctness.

module GC.Spec.Pages.Params

/// Words per page.
val page_wsize : pos

/// The number of size classes.
val n_cls : pos

/// The slot size of class `c`, in words, header included.
val cls (c: nat{c < n_cls}) : pos

/// The largest small block, in words, header included.
let small_max : pos = cls (n_cls - 1)

/// The conditions on the parameters.
let params_cond : prop =
  (* C1 *) cls 0 >= 2 /\
  (* C2 *) (forall (c: nat). c + 1 < n_cls ==> cls c < cls (c + 1)) /\
  (* C3 *) small_max <= page_wsize /\
  (* C4 *) page_wsize < pow2 20 /\
  (* C5 *) small_max > GC.Spec.SizeClass.n_small

val params_ok : unit -> Lemma params_cond
