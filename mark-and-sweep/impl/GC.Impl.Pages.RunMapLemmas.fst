/// ---------------------------------------------------------------------------
/// GC.Impl.Pages.RunMapLemmas - the run sweep's page map, built in two passes
/// ---------------------------------------------------------------------------
///
/// The specification's run sweep gives the run's pages new entries
/// (`GC.Spec.Pages.RunMap.new_map`): its whole free pages become free pages,
/// and each stretch of the others a swept run.  The Pulse run sweep builds
/// the map in two passes:
///   - while it lays out the run, each whole free page it writes gets a free
///     page's entry at once (`map_in`, `map_in_plain`, `map_in_page`);
///   - then a pass over the run's pages gives every other page its entry: the
///     first page of each stretch a run head with the stretch's length, the
///     others continuation entries (`pass2`, `pass2_free`, `pass2_head`,
///     `pass2_cont`, `pass2_done`).
/// A page is free after the first pass exactly when the layout freed it
/// (`freed_iff`), since every page of a run was a run page before.

module GC.Impl.Pages.RunMapLemmas

open GC.Spec.Base
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Inv
open GC.Spec.Pages.Blk
open GC.Spec.Pages.RunList
open GC.Spec.Pages.RunMap

module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

let set_entry (st: pstate) (i: nat{i < n_pages}) (e: page_info) : pstate =
  { st with pm = Seq.upd st.pm i e }

/// ---------------------------------------------------------------------------
/// The first pass
/// ---------------------------------------------------------------------------

/// The map once the blocks `xs` are laid out: their whole pages are free.
let map_in (st0 st: pstate) (xs: list blk) : prop =
  st.avail == st0.avail /\ st.atail == st0.atail /\ st.large == st0.large /\
  (forall (j: nat{j < n_pages}). entry st.pm j == (if L.mem (page_blk j) xs then free_entry else entry st0.pm j))

let map_in_start (st0: pstate) : Lemma (map_in st0 st0 []) = ()

let page_blk_inj (i j: nat) : Lemma (requires page_blk i == page_blk j) (ensures i == j)
  = page_base_lt i j; page_base_lt j i

#push-options "--fuel 2"
let map_in_plain (st0 st: pstate) (xs: list blk) (b: blk)
  : Lemma (requires map_in st0 st xs /\ b.t <> Page) (ensures map_in st0 st (L.append xs [b]))
  = let aux (j: nat{j < n_pages}) : Lemma (L.mem (page_blk j) (L.append xs [b]) == L.mem (page_blk j) xs)
      = L.append_mem xs [b] (page_blk j)
    in
    FStar.Classical.forall_intro aux

let map_in_page (st0 st: pstate) (xs: list blk) (j: nat{j < n_pages})
  : Lemma (requires map_in st0 st xs)
          (ensures map_in st0 (set_entry st j free_entry) (L.append xs [page_blk j]))
  = let aux (i: nat{i < n_pages})
      : Lemma (L.mem (page_blk i) (L.append xs [page_blk j]) == (L.mem (page_blk i) xs || i = j))
      = L.append_mem xs [page_blk j] (page_blk i);
        if page_blk i = page_blk j then page_blk_inj i j
    in
    FStar.Classical.forall_intro aux
#pop-options

/// ---------------------------------------------------------------------------
/// After the first pass
/// ---------------------------------------------------------------------------

/// No page outside the run is laid out.
let outside_not_freed (fs: list blk) (h n a: nat) (j: nat)
  : Lemma (requires contig fs (page_base h) a /\ a <= page_base (h + n) /\ (j < h \/ j >= h + n))
          (ensures not (freed fs j))
  = if freed fs j then begin
      contig_mem fs (page_base h) a (page_blk j);
      page_base_succ j;
      if j < h then page_base_lt j h else page_base_lt (h + n) (j + 1)
    end

/// The pages of the run are run pages before the sweep.
let run_pages (pm: page_map) (h: nat{h < n_pages}) (n: pos) : prop =
  (entry pm h).kind == LargeHead n /\ h + n <= n_pages /\
  (forall (j: nat). h < j /\ j < h + n ==> (entry pm j).kind == LargeCont)

/// After the first pass, a page of the run is free exactly when it is freed.
let freed_iff (st0 st1: pstate) (fs: list blk) (h: nat{h < n_pages}) (n: pos) (j: nat{j < n_pages})
  : Lemma (requires map_in st0 st1 fs /\ run_pages st0.pm h n /\ h <= j /\ j < h + n)
          (ensures ((entry st1.pm j).kind = Free) == freed fs j /\
                   (not (freed fs j) ==> entry st1.pm j == entry st0.pm j))
  = ()

/// ---------------------------------------------------------------------------
/// The second pass
/// ---------------------------------------------------------------------------

/// The pages before `jj` have their new entries; the rest are as the first
/// pass left them.
let pass2 (st0 st1 st: pstate) (fs: list blk) (h n jj: nat) : prop =
  st.avail == st0.avail /\ st.atail == st0.atail /\ st.large == st0.large /\
  (forall (j: nat{j < n_pages}).
     entry st.pm j == (if h <= j && j < jj then new_entry st0.pm fs h n j else entry st1.pm j))

let pass2_start (st0 st1: pstate) (fs: list blk) (h n: nat)
  : Lemma (requires map_in st0 st1 fs) (ensures pass2 st0 st1 st1 fs h n h)
  = ()

let run_from_step (fs: list blk) (j lim: nat)
  : Lemma (run_from fs j lim == (if j >= lim || freed fs j then 0 else 1 + run_from fs (j + 1) lim))
  = ()

/// A new entry is free exactly when its page is freed.
let new_free_iff (pm: page_map) (fs: list blk) (h n: nat) (j: nat{j < n_pages})
  : Lemma (requires h <= j /\ j < h + n)
          (ensures ((new_entry pm fs h n j).kind = Free) == freed fs j)
  = run_from_spec fs j (h + n)

/// One more page given its new entry `e`.
let pass2_upd (st0 st1 st: pstate) (fs: list blk) (h n: nat) (jj: nat{jj < n_pages}) (e: page_info)
  : Lemma (requires pass2 st0 st1 st fs h n jj /\ h <= jj /\ new_entry st0.pm fs h n jj == e)
          (ensures pass2 st0 st1 (set_entry st jj e) fs h n (jj + 1))
  = let aux (j: nat{j < n_pages})
      : Lemma (entry (set_entry st jj e).pm j ==
               (if h <= j && j < jj + 1 then new_entry st0.pm fs h n j else entry st1.pm j))
      = if j = jj then () else assert (entry (set_entry st jj e).pm j == entry st.pm j)
    in
    FStar.Classical.forall_intro aux

let pass2_free (st0 st1 st: pstate) (fs: list blk) (h: nat{h < n_pages}) (n: pos) (jj: nat{jj < n_pages})
  : Lemma (requires pass2 st0 st1 st fs h n jj /\ map_in st0 st1 fs /\ run_pages st0.pm h n /\
                    h <= jj /\ jj < h + n /\ freed fs jj)
          (ensures pass2 st0 st1 st fs h n (jj + 1))
  = assert (new_entry st0.pm fs h n jj == free_entry);
    assert (entry st.pm jj == free_entry);
    let aux (j: nat{j < n_pages})
      : Lemma (entry st.pm j == (if h <= j && j < jj + 1 then new_entry st0.pm fs h n j else entry st1.pm j))
      = ()
    in
    FStar.Classical.forall_intro aux

/// The entry of the first page of a stretch.
let new_head (st0 st1: pstate) (fs: list blk) (h: nat{h < n_pages}) (n: pos) (jj: nat{jj < n_pages}) (m: nat)
  : Lemma (requires map_in st0 st1 fs /\ run_pages st0.pm h n /\
                    h <= jj /\ jj < h + n /\ not (freed fs jj) /\
                    (jj = h \/ freed fs (jj - 1)) /\ m == run_from fs jj (h + n))
          (ensures m > 0 /\
                   new_entry st0.pm fs h n jj == { entry st1.pm jj with kind = LargeHead m; swept = true })
  = run_from_spec fs jj (h + n);
    freed_iff st0 st1 fs h n jj

let pass2_head (st0 st1 st: pstate) (fs: list blk) (h: nat{h < n_pages}) (n: pos) (jj: nat{jj < n_pages}) (m: nat)
  : Lemma (requires pass2 st0 st1 st fs h n jj /\ map_in st0 st1 fs /\ run_pages st0.pm h n /\
                    h <= jj /\ jj < h + n /\ not (freed fs jj) /\
                    (jj = h \/ freed fs (jj - 1)) /\ m == run_from fs jj (h + n))
          (ensures m > 0 /\
                   pass2 st0 st1 (set_entry st jj ({ entry st1.pm jj with kind = LargeHead m; swept = true }))
                         fs h n (jj + 1))
  = new_head st0 st1 fs h n jj m;
    pass2_upd st0 st1 st fs h n jj ({ entry st1.pm jj with kind = LargeHead m; swept = true })

/// The entry of a later page of a stretch.
let new_cont (st0 st1: pstate) (fs: list blk) (h: nat{h < n_pages}) (n: pos) (jj: nat{jj < n_pages})
  : Lemma (requires map_in st0 st1 fs /\ run_pages st0.pm h n /\
                    h < jj /\ jj < h + n /\ not (freed fs jj) /\ not (freed fs (jj - 1)))
          (ensures new_entry st0.pm fs h n jj == { entry st1.pm jj with kind = LargeCont; swept = true })
  = freed_iff st0 st1 fs h n jj

let pass2_cont (st0 st1 st: pstate) (fs: list blk) (h: nat{h < n_pages}) (n: pos) (jj: nat{jj < n_pages})
  : Lemma (requires pass2 st0 st1 st fs h n jj /\ map_in st0 st1 fs /\ run_pages st0.pm h n /\
                    h < jj /\ jj < h + n /\ not (freed fs jj) /\ not (freed fs (jj - 1)))
          (ensures pass2 st0 st1 (set_entry st jj ({ entry st1.pm jj with kind = LargeCont; swept = true }))
                         fs h n (jj + 1))
  = new_cont st0 st1 fs h n jj;
    pass2_upd st0 st1 st fs h n jj ({ entry st1.pm jj with kind = LargeCont; swept = true })

/// The page before `jj` is free after the second pass exactly when it is
/// freed.
let pass2_prev (st0 st1 st: pstate) (fs: list blk) (h: nat{h < n_pages}) (n: pos) (jj: nat{jj < n_pages})
  : Lemma (requires pass2 st0 st1 st fs h n jj /\ h < jj /\ jj < h + n)
          (ensures ((entry st.pm (jj - 1)).kind = Free) == freed fs (jj - 1))
  = new_free_iff st0.pm fs h n (jj - 1)

/// The pages from `jj` on are as the first pass left them.
let pass2_ahead (st0 st1 st: pstate) (fs: list blk) (h n jj: nat) (k: nat{k < n_pages})
  : Lemma (requires pass2 st0 st1 st fs h n jj /\ k >= jj) (ensures entry st.pm k == entry st1.pm k)
  = ()

let pass2_done (st0 st1 st: pstate) (fs: list blk) (h: nat{h < n_pages}) (n: pos) (a: nat)
  : Lemma (requires pass2 st0 st1 st fs h n (h + n) /\ map_in st0 st1 fs /\
                    contig fs (page_base h) a /\ a <= page_base (h + n))
          (ensures st.pm == new_map st0.pm fs h n)
  = let aux (j: nat{j < n_pages}) : Lemma (Seq.index st.pm j == Seq.index (new_map st0.pm fs h n) j)
      = new_map_entry st0.pm fs h n j;
        if j < h || j >= h + n then outside_not_freed fs h n a j
    in
    FStar.Classical.forall_intro aux;
    Seq.lemma_eq_intro st.pm (new_map st0.pm fs h n)
