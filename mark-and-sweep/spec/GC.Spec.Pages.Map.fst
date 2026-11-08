/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Map - the page map: what each page is used for
/// ---------------------------------------------------------------------------
///
/// The page map is a side table with one entry per page, outside the heap.
/// A page is
///   - `Free`: one blue block covering the page, on no list;
///   - `Pool c`: slots of class `c` (GC.Spec.Pages.Layout);
///   - `LargeHead n`: the first of the `n` pages of a large run, a stretch of
///     the large-object area that the walk tiles on its own;
///   - `LargeCont`: a later page of a large run.
///
/// Each entry also says whether the page is swept.  Between collections every
/// page is swept.  A free page is always swept: it holds nothing to sweep.
/// A run's pages are swept together.
///
/// `free_head`, `nfree` and `next` serve pool pages: the head of the page's
/// free-slot list, its length, and the link in the class's list of pages
/// with a free slot (`GC.Spec.Pages.Inv`).

module GC.Spec.Pages.Map

open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout

module U64 = FStar.UInt64
module Seq = FStar.Seq

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

type page_kind =
  | Free
  | Pool : c: nat{c < n_cls} -> page_kind
  | LargeHead : n: pos -> page_kind
  | LargeCont

type page_info = {
  kind: page_kind;
  swept: bool;
  free_head: U64.t;
  nfree: nat;
  next: U64.t;
}

/// The length of a run.
let run_len (k: page_kind{LargeHead? k}) : pos = match k with LargeHead n -> n

/// The ghost page map: one entry per page.
let page_map = pm: Seq.seq page_info{Seq.length pm == n_pages}

let entry (pm: page_map) (i: nat{i < n_pages}) : page_info = Seq.index pm i

/// The first page of a run of `n` pages.
let is_head (pm: page_map) (i: nat{i < n_pages}) (n: pos) : bool =
  LargeHead? (entry pm i).kind && run_len (entry pm i).kind = n

/// Page `j` lies in a run that starts at page `h`.
let in_run (pm: page_map) (h: nat{h < n_pages}) (j: nat) : bool =
  LargeHead? (entry pm h).kind && h <= j && j < h + run_len (entry pm h).kind

/// A run fits in the heap, its later pages are continuation pages, and they
/// share the run's swept state.
let run_ok (pm: page_map) (i: nat{i < n_pages}) : prop =
  LargeHead? (entry pm i).kind ==>
  (let n = run_len (entry pm i).kind in
   i + n <= n_pages /\
   (forall (j: nat). i < j /\ j < i + n ==>
      (entry pm j).kind == LargeCont /\ (entry pm j).swept == (entry pm i).swept))

/// A continuation page belongs to a run.
let cont_ok (pm: page_map) (j: nat{j < n_pages}) : prop =
  (entry pm j).kind == LargeCont ==>
  (exists (h: nat{h < n_pages}). h < j /\ in_run pm h j)

/// A free page is swept.
let free_ok (pm: page_map) (i: nat{i < n_pages}) : prop =
  (entry pm i).kind == Free ==> (entry pm i).swept == true

let map_ok (pm: page_map) : prop =
  forall (i: nat{i < n_pages}). run_ok pm i /\ cont_ok pm i /\ free_ok pm i

/// A page where the walk starts a page's worth of blocks: any page that does
/// not continue a run, and the end of the pages.
let walk_page (pm: page_map) (j: nat{j <= n_pages}) : bool =
  j = n_pages || (entry pm j).kind <> LargeCont

/// How many pages the walk from page `i` covers before the next walk page.
let span (pm: page_map) (i: nat{i < n_pages}) : pos =
  match (entry pm i).kind with
  | LargeHead n -> n
  | _ -> 1

/// The next walk page after a walk page is `i + span`, and nothing between
/// them is a walk page.
let next_walk_page (pm: page_map) (i: nat{i < n_pages}) (j: nat{j <= n_pages})
  : Lemma (requires map_ok pm /\ walk_page pm i)
          (ensures i + span pm i <= n_pages /\
                   (i + span pm i < n_pages ==> walk_page pm (i + span pm i)) /\
                   (i < j /\ j < i + span pm i ==> not (walk_page pm j)))
  = assert (run_ok pm i);
    let i' = i + span pm i in
    if i' < n_pages && (entry pm i').kind = LargeCont then begin
      assert (cont_ok pm i');
      eliminate exists (h: nat{h < n_pages}). h < i' /\ in_run pm h i'
      with begin
        assert (run_ok pm h);
        if h < i then assert ((entry pm i).kind == LargeCont)
        else if h = i then ()
        else assert ((entry pm h).kind == LargeCont)
      end
    end

/// ---------------------------------------------------------------------------
/// Vacuity: the map of an empty heap
/// ---------------------------------------------------------------------------

let free_entry : page_info =
  { kind = Free; swept = true; free_head = 0UL; nfree = 0; next = 0UL }

let all_free : page_map = Seq.create n_pages free_entry

let all_free_ok () : Lemma (map_ok all_free) = ()
