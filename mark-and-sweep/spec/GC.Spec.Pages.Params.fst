module GC.Spec.Pages.Params

/// The two candidate page sizes (docs/pages-allocator-proof-plan.md).  Both
/// are checked against the conditions below; `page_wsize` picks one.
let page_wsize_16k : pos = 2048
let page_wsize_32k : pos = 4096

let page_wsize = page_wsize_32k

/// OCaml 5's `wsize_sizeclass` (runtime/caml/sizeclasses.h) without its
/// 1-word class: the smallest class is 2 words, and a 1-word block takes a
/// 2-word slot.
let cls_list : list pos =
  [2; 3; 4; 5; 6; 7; 8; 10; 12; 14; 16; 17; 19; 22; 25; 28; 32; 33; 37; 42;
   47; 53; 59; 65; 73; 81; 89; 99; 108; 118; 128]

let n_cls = 31

let cls c =
  assert_norm (FStar.List.Tot.length cls_list == n_cls);
  FStar.List.Tot.index cls_list c

/// C2, checked one neighbouring pair at a time.
let rec increasing_from (c: nat) : Tot bool (decreases (n_cls - c)) =
  if c + 1 >= n_cls then true
  else cls c < cls (c + 1) && increasing_from (c + 1)

let rec increasing_from_spec (c: nat) (d: nat)
  : Lemma (requires increasing_from c /\ c <= d /\ d + 1 < n_cls)
          (ensures cls d < cls (d + 1))
          (decreases (d - c))
  = if c = d then () else increasing_from_spec (c + 1) d

/// The conditions hold at a given page size.
let cond_at (pw: pos) : bool =
  cls 0 >= 2 && increasing_from 0 && cls (n_cls - 1) <= pw && pw < pow2 20

let both_candidates_ok () : Lemma (cond_at page_wsize_16k /\ cond_at page_wsize_32k)
  = assert_norm (cond_at page_wsize_16k);
    assert_norm (cond_at page_wsize_32k)

let increasing (c: nat)
  : Lemma (c + 1 < n_cls ==> cls c < cls (c + 1))
  = both_candidates_ok ();
    if c + 1 < n_cls then increasing_from_spec 0 c

let large_beyond_small_lists () : Lemma (cls (n_cls - 1) > GC.Spec.SizeClass.n_small)
  = reveal_opaque (`%GC.Spec.SizeClass.n_small) GC.Spec.SizeClass.n_small;
    assert_norm (cls (n_cls - 1) == 128)

let params_ok () =
  both_candidates_ok ();
  large_beyond_small_lists ();
  FStar.Classical.forall_intro increasing
