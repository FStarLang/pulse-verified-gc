/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Frame - what an allocator step leaves alone
/// ---------------------------------------------------------------------------
///
/// The clauses of `pages_ok` are of three kinds:
///   - page-local (`page_local`): a page's shape, its free-slot list, its
///     colours.  They read only the page's entry and the words of its span
///     (one page, or a whole run), so a step that leaves both alone keeps them
///     (`page_local_frame`);
///   - the page lists (`avail_ok`): they read only entries of pages with a
///     free slot (`avail_frame`);
///   - the large lists (`large_ok`) and `no_pointer_to_blue`, handled with
///     `GC.Spec.Pages.Cells` and `GC.Spec.Pages.Replace`.

module GC.Spec.Pages.Frame

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Walk
open GC.Spec.Pages.Shape
open GC.Spec.Pages.Inv

module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Ranges of words
/// ---------------------------------------------------------------------------

let kept_range (g g': heap) (lo hi: nat) : prop =
  forall (x: hp_addr). lo <= U64.v x /\ U64.v x < hi ==> read_word g' x == read_word g x

let kept_hdr (g g': heap) (lo hi: nat) (x: nat)
  : Lemma (requires kept_range g g' lo hi /\ lo <= x /\ x < hi)
          (ensures hdr g' x == hdr g x /\ words_at g' x == words_at g x /\
                   color_at g' x == color_at g x)
  = if x < heap_size && x % 8 = 0 then assert (read_word g' (mk_hp_addr x) == read_word g (mk_hp_addr x))

let kept_sub (g g': heap) (lo hi lo' hi': nat)
  : Lemma (requires kept_range g g' lo hi /\ lo <= lo' /\ hi' <= hi)
          (ensures kept_range g g' lo' hi')
  = ()

/// The last page of the span that starts at page `i`, plus one.
let span_end (pm: page_map) (i: nat{i < n_pages}) : nat =
  match (entry pm i).kind with
  | LargeHead n -> i + n
  | _ -> i + 1

/// ---------------------------------------------------------------------------
/// The page-local clauses
/// ---------------------------------------------------------------------------

let page_local (g: heap) (pm: page_map) (i: nat{i < n_pages}) : prop =
  page_shape g pm i /\ pool_list_ok g pm i /\ pool_white g pm i /\ run_swept_ok g pm i

/// Every word a slot's clauses read lies in its page.
let slot_reads (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat{k < n_slots c})
  : Lemma (let a = slot_base i c k in
           page_base i <= a /\ a + 8 < page_base (i + 1) /\
           (words_at g a < cls c ==> a + words_at g a * 8 < page_base (i + 1)))
  = slot_in_page i c k;
    slots_fill_page i c;
    cls_bounds c

/// The words of slot `k`.
let slot_end (i: nat) (c: nat{c < n_cls}) (k: nat) : nat = slot_base i c k + cls c * 8

let slot_kept (g g': heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat{k < n_slots c})
  : Lemma (requires kept_range g g' (page_base i) (page_base (i + 1)))
          (ensures kept_range g g' (slot_base i c k) (slot_end i c k))
  = slot_in_page i c k;
    slots_fill_page i c

let slot_frame (g g': heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat{k < n_slots c})
  : Lemma (requires kept_range g g' (slot_base i c k) (slot_end i c k))
          (ensures (slot_free g' i c k <==> slot_free g i c k) /\
                   (slot_used g' i c k <==> slot_used g i c k) /\
                   color_at g' (slot_base i c k) == color_at g (slot_base i c k) /\
                   hdr g' (slot_obj i c k) == hdr g (slot_obj i c k))
  = let a = slot_base i c k in
    let e = slot_end i c k in
    cls_bounds c;
    kept_hdr g g' a e a;
    kept_hdr g g' a e (a + 8);
    if words_at g a < cls c then kept_hdr g g' a e (a + words_at g a * 8)

let pool_shape_frame (g g': heap) (i: nat{i < n_pages}) (c: nat{c < n_cls})
  : Lemma (requires kept_range g g' (page_base i) (page_base (i + 1)) /\ pool_shape g i c)
          (ensures pool_shape g' i c)
  = let aux (k: nat) : Lemma (k < n_slots c ==> slot_ok g' i c k)
      = if k < n_slots c then (slot_kept g g' i c k; slot_frame g g' i c k)
    in
    FStar.Classical.forall_intro aux;
    slots_fill_page i c;
    if tail_words c > 0 then kept_hdr g g' (page_base i) (page_base (i + 1)) (slots_end i c)

#push-options "--fuel 1"
let rec slot_chain_frame (g g': heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (hd: U64.t) (ks: list nat)
  : Lemma (requires kept_range g g' (page_base i) (page_base (i + 1)) /\ slot_chain g i c hd ks)
          (ensures slot_chain g' i c hd ks)
          (decreases ks)
  = match ks with
    | [] -> ()
    | k :: ks' ->
      slot_kept g g' i c k;
      slot_frame g g' i c k;
      slot_chain_frame g g' i c (hdr g (slot_obj i c k)) ks'
#pop-options

let pool_list_frame (g g': heap) (pm pm': page_map) (i: nat{i < n_pages})
  : Lemma (requires kept_range g g' (page_base i) (page_base (i + 1)) /\
                    entry pm' i == entry pm i /\ pool_list_ok g pm i)
          (ensures pool_list_ok g' pm' i)
  = match (entry pm i).kind with
    | Pool c ->
      if (entry pm i).swept then
        eliminate exists (ks: list nat).
          slot_chain g i c (entry pm i).free_head ks /\ L.noRepeats ks /\
          (forall (k: nat). k < n_slots c ==> (L.mem k ks <==> slot_free g i c k)) /\
          (entry pm i).nfree == L.length ks
        with begin
          slot_chain_frame g g' i c (entry pm i).free_head ks;
          let aux (k: nat) : Lemma (k < n_slots c ==> (slot_free g' i c k <==> slot_free g i c k))
            = if k < n_slots c then (slot_kept g g' i c k; slot_frame g g' i c k)
          in
          FStar.Classical.forall_intro aux
        end
    | _ -> ()

let pool_white_frame (g g': heap) (pm pm': page_map) (i: nat{i < n_pages})
  : Lemma (requires kept_range g g' (page_base i) (page_base (i + 1)) /\
                    entry pm' i == entry pm i /\ pool_white g pm i)
          (ensures pool_white g' pm' i)
  = match (entry pm i).kind with
    | Pool c ->
      let aux (k: nat) : Lemma (k < n_slots c ==>
                                (slot_used g' i c k <==> slot_used g i c k) /\
                                color_at g' (slot_base i c k) == color_at g (slot_base i c k))
        = if k < n_slots c then (slot_kept g g' i c k; slot_frame g g' i c k)
      in
      FStar.Classical.forall_intro aux
    | _ -> ()

/// The blocks of a run, and what they read, are kept with the run's words.
let run_block_frame (g g': heap) (h: nat) (n: pos) (a: nat)
  : Lemma (requires kept_range g g' (page_base h) (page_base (h + n)))
          (ensures (run_block g' h n a <==> run_block g h n a) /\
                   (run_block g h n a ==>
                      color_at g' a == color_at g a /\ words_at g' a == words_at g a /\
                      (a + words_at g a * 8 < page_base (h + n) ==>
                         color_at g' (a + words_at g a * 8) == color_at g (a + words_at g a * 8))))
  = if a <= page_base (h + n) then steps_to_frame g g' (page_base h) a;
    if run_block g h n a then begin
      steps_to_le g (page_base h) a;
      kept_hdr g g' (page_base h) (page_base (h + n)) a;
      let nx = a + words_at g a * 8 in
      if nx < page_base (h + n) then
        kept_hdr g g' (page_base h) (page_base (h + n)) nx
    end

let run_swept_frame (g g': heap) (pm pm': page_map) (i: nat{i < n_pages})
  : Lemma (requires kept_range g g' (page_base i) (page_base (span_end pm i)) /\
                    entry pm' i == entry pm i /\ run_swept_ok g pm i)
          (ensures run_swept_ok g' pm' i)
  = match (entry pm i).kind with
    | LargeHead n ->
      FStar.Classical.forall_intro (FStar.Classical.move_requires (run_block_frame g g' i n))
    | _ -> ()

let page_shape_frame (g g': heap) (pm pm': page_map) (i: nat{i < n_pages})
  : Lemma (requires kept_range g g' (page_base i) (page_base (span_end pm i)) /\
                    entry pm' i == entry pm i /\ page_shape g pm i)
          (ensures page_shape g' pm' i)
  = match (entry pm i).kind with
    | Free -> kept_hdr g g' (page_base i) (page_base (i + 1)) (page_base i)
    | Pool c -> pool_shape_frame g g' i c
    | LargeHead n -> steps_to_frame g g' (page_base i) (page_base (i + n))
    | LargeCont -> ()

/// **A page whose entry and span are left alone keeps its clauses.**
let page_local_frame (g g': heap) (pm pm': page_map) (i: nat{i < n_pages})
  : Lemma (requires kept_range g g' (page_base i) (page_base (span_end pm i)) /\
                    entry pm' i == entry pm i /\ page_local g pm i)
          (ensures page_local g' pm' i)
  = page_shape_frame g g' pm pm' i;
    run_swept_frame g g' pm pm' i;
    if not (LargeHead? (entry pm i).kind) then begin
      pool_list_frame g g' pm pm' i;
      pool_white_frame g g' pm pm' i
    end

let tail_frame (g g': heap)
  : Lemma (requires kept_range g g' pages_end heap_size /\ tail_shape g)
          (ensures tail_shape g')
  = if heap_size - pages_end >= 16 then begin
      pages_end_bound ();
      kept_hdr g g' pages_end heap_size pages_end
    end

/// ---------------------------------------------------------------------------
/// The page lists
/// ---------------------------------------------------------------------------

#push-options "--fuel 1"
let rec page_chain_frame (pm pm': page_map) (hd: U64.t) (ps: list nat)
  : Lemma (requires page_chain pm hd ps /\
                    (forall (q: nat{q < n_pages}). L.mem q ps ==> (entry pm' q).next == (entry pm q).next))
          (ensures page_chain pm' hd ps)
          (decreases ps)
  = match ps with
    | [] -> ()
    | p :: ps' -> page_chain_frame pm pm' (entry pm p).next ps'
#pop-options

/// The page lists are kept when the pages with a free slot, and their links,
/// are.
let avail_frame (st st': pstate)
  : Lemma (requires avail_ok st /\ st'.avail == st.avail /\
                    (forall (c: nat{c < n_cls}) (q: nat{q < n_pages}).
                       has_free_slot st'.pm c q == has_free_slot st.pm c q /\
                       (has_free_slot st.pm c q ==> (entry st'.pm q).next == (entry st.pm q).next)))
          (ensures avail_ok st')
  = let aux (c: nat{c < n_cls})
      : Lemma (exists (ps: list nat).
                 page_chain st'.pm (Seq.index st'.avail c) ps /\ L.noRepeats ps /\
                 (forall (p: nat{p < n_pages}). L.mem p ps <==> has_free_slot st'.pm c p))
      = eliminate exists (ps: list nat).
          page_chain st.pm (Seq.index st.avail c) ps /\ L.noRepeats ps /\
          (forall (p: nat{p < n_pages}). L.mem p ps <==> has_free_slot st.pm c p)
        with page_chain_frame st.pm st'.pm (Seq.index st.avail c) ps
    in
    FStar.Classical.forall_intro aux

/// ---------------------------------------------------------------------------
/// Runs and pages
/// ---------------------------------------------------------------------------

/// An address in pages `h .. h + n - 1` lies in one of them.
let in_pages (h: nat) (n: pos) (i: nat) (a: nat)
  : Lemma (requires page_base h <= a /\ a < page_base (h + n) /\ in_page i a)
          (ensures h <= i /\ i < h + n)
  = if i < h then FStar.Math.Lemmas.lemma_mult_le_right page_bytes (i + 1) h;
    if i >= h + n then FStar.Math.Lemmas.lemma_mult_le_right page_bytes (h + n) i

/// A swept run lies in run pages: an address of a free or pool page is not
/// in one.
let not_in_run (pm: page_map) (i: nat{i < n_pages}) (a: nat)
  : Lemma (requires map_ok pm /\ in_page i a /\ in_swept_run pm a /\
                    ~(LargeHead? (entry pm i).kind) /\ (entry pm i).kind =!= LargeCont)
          (ensures False)
  = eliminate exists (h: nat{h < n_pages}).
      LargeHead? (entry pm h).kind /\ (entry pm h).swept /\
      page_base h <= a /\ a < page_base (h + run_len (entry pm h).kind)
    with begin
      in_pages h (run_len (entry pm h).kind) i a;
      assert (run_ok pm h)
    end
