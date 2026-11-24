/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.RunMap - the page map after a run is swept
/// ---------------------------------------------------------------------------
///
/// After the run of `n` pages at page `h` is swept, some of its pages are
/// free (`freed`: the swept layout holds the page as one free block).  The
/// other pages fall into maximal stretches, and each stretch becomes a run
/// of its own: its first page is the head, the others continue it.  Every
/// entry of the run's pages is swept; every other entry is unchanged.
///
/// `new_map_ok` shows the map stays well formed (`map_ok`), and
/// `head_facts`/`cont_head` give what the run sweep's proof needs about
/// each new run: it lies in the old run, holds no free page, and begins and
/// ends at the old run's ends or next to a free page.

module GC.Spec.Pages.RunMap

open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Blk
open GC.Spec.Pages.RunList

module Seq = FStar.Seq
module L = FStar.List.Tot

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

/// Page `j` is a free page of the layout `fs`.
let freed (fs: list blk) (j: nat) : bool = L.mem (page_blk j) fs

/// The pages from `j` on, before `lim`, that are not free.
let rec run_from (fs: list blk) (j lim: nat) : Tot nat (decreases (if j < lim then lim - j else 0)) =
  if j >= lim || freed fs j then 0 else 1 + run_from fs (j + 1) lim

let new_entry (pm: page_map) (fs: list blk) (h n: nat) (j: nat{j < n_pages}) : page_info =
  let old = entry pm j in
  if j < h || j >= h + n then old
  else if freed fs j then free_entry
  else if j = h || freed fs (j - 1) then begin
    let m = run_from fs j (h + n) in
    if m > 0 then { old with kind = LargeHead m; swept = true } else free_entry
  end
  else { old with kind = LargeCont; swept = true }

let new_map (pm: page_map) (fs: list blk) (h n: nat) : page_map =
  Seq.init n_pages (new_entry pm fs h n)

let new_map_entry (pm: page_map) (fs: list blk) (h n: nat) (j: nat{j < n_pages})
  : Lemma (entry (new_map pm fs h n) j == new_entry pm fs h n j)
  = ()

/// ---------------------------------------------------------------------------
/// Stretches of pages that are not free
/// ---------------------------------------------------------------------------

let rec run_from_spec (fs: list blk) (j lim: nat)
  : Lemma (ensures (let m = run_from fs j lim in
                    (j < lim /\ not (freed fs j) ==> m > 0) /\
                    (m > 0 ==> j + m <= lim) /\
                    (forall (k: nat). j <= k /\ k < j + m ==> not (freed fs k)) /\
                    (m > 0 /\ j + m < lim ==> freed fs (j + m))))
          (decreases (if j < lim then lim - j else 0))
  = if j >= lim || freed fs j then () else run_from_spec fs (j + 1) lim

/// From a page that is not free, back to the start of its stretch.
let rec head_back (fs: list blk) (h: nat) (k: nat)
  : Pure nat (requires h <= k /\ not (freed fs k))
             (ensures fun u -> h <= u /\ u <= k /\ (u = h \/ freed fs (u - 1)) /\
                               (forall (i: nat). u <= i /\ i <= k ==> not (freed fs i)))
             (decreases k)
  = if k = h || freed fs (k - 1) then k else head_back fs h (k - 1)

let run_from_reach (fs: list blk) (u k lim: nat)
  : Lemma (requires u <= k /\ k < lim /\ (forall (i: nat). u <= i /\ i <= k ==> not (freed fs i)))
          (ensures k < u + run_from fs u lim)
  = run_from_spec fs u lim;
    if u + run_from fs u lim <= k then run_from_spec fs u lim

/// ---------------------------------------------------------------------------
/// The new runs
/// ---------------------------------------------------------------------------

let in_old (h n j: nat) : bool = h <= j && j < h + n

/// A head of a new run.
let head_facts (pm: page_map) (fs: list blk) (h n: nat) (j: nat{j < n_pages})
  : Lemma (requires in_old h n j /\ LargeHead? (entry (new_map pm fs h n) j).kind)
          (ensures (let m = run_len (entry (new_map pm fs h n) j).kind in
                    m == run_from fs j (h + n) /\ j + m <= h + n /\
                    not (freed fs j) /\ (j = h \/ freed fs (j - 1)) /\
                    (forall (k: nat). j <= k /\ k < j + m ==> not (freed fs k)) /\
                    (j + m = h + n \/ freed fs (j + m))))
  = run_from_spec fs j (h + n)

/// A free page of the new map.
let free_facts (pm: page_map) (fs: list blk) (h n: nat) (j: nat{j < n_pages})
  : Lemma (requires in_old h n j /\ (entry (new_map pm fs h n) j).kind == Free)
          (ensures freed fs j)
  = run_from_spec fs j (h + n)

/// The new map's entries in the run are swept, and free or run pages.
let in_facts (pm: page_map) (fs: list blk) (h n: nat) (j: nat{j < n_pages})
  : Lemma (requires in_old h n j)
          (ensures (entry (new_map pm fs h n) j).swept == true /\
                   ~(Pool? (entry (new_map pm fs h n) j).kind) /\
                   (freed fs j <==> (entry (new_map pm fs h n) j).kind == Free))
  = run_from_spec fs j (h + n)

/// A continuation page of the new map lies in a new run.
let cont_head (pm: page_map) (fs: list blk) (h n: nat) (j: nat{j < n_pages})
  : Lemma (requires in_old h n j /\ (entry (new_map pm fs h n) j).kind == LargeCont /\ h + n <= n_pages)
          (ensures exists (u: nat{u < n_pages}). h <= u /\ u < j /\ in_run (new_map pm fs h n) u j)
  = let pm' = new_map pm fs h n in
    run_from_spec fs j (h + n);
    assert (j > h /\ not (freed fs (j - 1)) /\ not (freed fs j));
    let u = head_back fs h (j - 1) in
    run_from_reach fs u j (h + n);
    run_from_spec fs u (h + n);
    assert (LargeHead? (entry pm' u).kind);
    assert (in_run pm' u j)

/// ---------------------------------------------------------------------------
/// The map stays well formed
/// ---------------------------------------------------------------------------

/// A run of the old map other than the swept one lies wholly outside it.
let other_run (pm: page_map) (h: nat{h < n_pages}) (n: pos) (u: nat{u < n_pages})
  : Lemma (requires map_ok pm /\ (entry pm h).kind == LargeHead n /\ LargeHead? (entry pm u).kind /\ u <> h)
          (ensures u + run_len (entry pm u).kind <= h \/ u >= h + n)
  = assert (run_ok pm h);
    assert (run_ok pm u);
    if u < h && h < u + run_len (entry pm u).kind then assert ((entry pm h).kind == LargeCont)
    else if h < u && u < h + n then assert ((entry pm u).kind == LargeCont)

let new_map_ok (pm: page_map) (fs: list blk) (h: nat{h < n_pages}) (n: pos)
  : Lemma (requires map_ok pm /\ (entry pm h).kind == LargeHead n)
          (ensures map_ok (new_map pm fs h n) /\
                   (forall (j: nat{j < n_pages}). ~(in_old h n j) ==> entry (new_map pm fs h n) j == entry pm j))
  = let pm' = new_map pm fs h n in
    assert (run_ok pm h);
    let aux (j: nat{j < n_pages}) : Lemma (run_ok pm' j /\ cont_ok pm' j /\ free_ok pm' j)
      = assert (run_ok pm j /\ cont_ok pm j /\ free_ok pm j);
        if in_old h n j then begin
          in_facts pm fs h n j;
          (match (entry pm' j).kind with
           | LargeHead m ->
             head_facts pm fs h n j;
             let cont (k: nat) : Lemma (j < k /\ k < j + m ==>
                                        (entry pm' k).kind == LargeCont /\ (entry pm' k).swept == (entry pm' j).swept)
               = if j < k && k < j + m then in_facts pm fs h n k
             in
             FStar.Classical.forall_intro cont
           | LargeCont -> cont_head pm fs h n j
           | _ -> ())
        end else begin
          (match (entry pm j).kind with
           | LargeHead m ->
             other_run pm h n j;
             assert (forall (k: nat). j < k /\ k < j + m ==> ~(in_old h n k))
           | LargeCont ->
             eliminate exists (u: nat{u < n_pages}). u < j /\ in_run pm u j
             with begin
               if u = h then ()
               else begin
                 other_run pm h n u;
                 assert (~(in_old h n u));
                 assert (in_run pm' u j)
               end
             end
           | _ -> ())
        end
    in
    FStar.Classical.forall_intro aux
