/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.SweepPage - sweeping one pool page
/// ---------------------------------------------------------------------------
///
/// `sweep_page g pm i` sweeps the pool page `i` as OCaml 5's `pool_sweep`
/// does, reading and writing slot starts only:
///   - a slot whose header is black holds a survivor: its header is made
///     white, and the rest of the slot (fields, filler) is left alone;
///   - any other slot becomes a free slot: a blue header of the class size,
///     its first field linking to the free slot before it (0 for the first);
///   - a page left with no survivor becomes a free page, one blue block: its
///     first word, over the swept slots, becomes a blue header covering the
///     page.  So the sweep is one pass over the slots, as `pool_sweep` is,
///     and it knows whether the page had a survivor when the pass ends
///     (`dead_count`: fewer free slots than slots).
/// The page tail is never written.  Only page `i`'s words change, and only
/// its entry; the entry is swept, and a page with a survivor keeps its `next`
/// link, which the caller sets when it puts the page on its class's list
/// (`GC.Spec.Pages.SweepAll`).
///
/// `sweep_page_correct` proves `sweep_page_meets sweep_page`
/// (`GC.Spec.Pages.Theorems`).  The proof reads the swept heap back slot by
/// slot (`sw_hd`, `sw_link`, `sw_out`, `sw_rest`), then follows the free
/// slots from the last one down (`dead_chain`).

module GC.Spec.Pages.SweepPage

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Shape
open GC.Spec.Pages.Inv
open GC.Spec.Pages.Init
open GC.Spec.Pages.PoolInit
open GC.Spec.Pages.Theorems

module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The sweep
/// ---------------------------------------------------------------------------

/// Slot `k` holds a survivor: its header is black.
let live (g: heap) (i: nat) (c: nat{c < n_cls}) (k: nat) : bool =
  color_at g (slot_base i c k) = Black

/// The free slots among `0 .. k-1`, the last first: the free-slot list the
/// sweep has built when it has passed them.
#push-options "--fuel 1"
let rec dead_list (g: heap) (i: nat) (c: nat{c < n_cls}) (k: nat) : Tot (list nat) (decreases k) =
  if k = 0 then []
  else if live g i c (k - 1) then dead_list g i c (k - 1)
  else (k - 1) :: dead_list g i c (k - 1)
#pop-options

/// The head of that list.
let hd_upto (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat) : U64.t =
  match dead_list g i c k with
  | [] -> 0UL
  | j :: _ -> if j < n_slots c then (slot_link i c j <: U64.t) else 0UL

/// The swept slots `0 .. k-1`.
#push-options "--fuel 1"
let rec sw_heap (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat{k <= n_slots c})
  : GTot heap (decreases k)
  = if k = 0 then g
    else begin
      let j = k - 1 in
      let g1 = sw_heap g i c j in
      let a = slot_hd i c j in
      if live g i c j then write_word g1 a (colorHeader (read_word g a) White)
      else write_word (write_word g1 a (slot_hdr c)) (slot_link i c j) (hd_upto g i c j)
    end
#pop-options

/// Some slot holds a survivor.
let page_live (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) : prop =
  exists (k: nat). k < n_slots c /\ live g i c k

/// The swept page, when it holds a survivor.
let pool_swept (g: heap) (pm: page_map) (i: nat{i < n_pages}) (c: nat{c < n_cls}) : GTot (heap & page_info) =
  (sw_heap g i c (n_slots c),
   { kind = Pool c; swept = true; free_head = hd_upto g i c (n_slots c);
     nfree = L.length (dead_list g i c (n_slots c)); next = (entry pm i).next })

/// The page given back as a free page: the swept slots, then one blue header
/// over the page.
let page_freed (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) : GTot (heap & page_info) =
  cls_bounds 0;
  (write_word (sw_heap g i c (n_slots c)) (page_addr i) page_hdr, free_entry)

#push-options "--fuel 1"
let rec any_live (g: heap) (i: nat) (c: nat{c < n_cls}) (k: nat) : Tot bool (decreases k) =
  if k = 0 then false else live g i c (k - 1) || any_live g i c (k - 1)

let rec any_live_spec (g: heap) (i: nat) (c: nat{c < n_cls}) (k: nat)
  : Lemma (ensures any_live g i c k <==> (exists (j: nat). j < k /\ live g i c j)) (decreases k)
  = if k > 0 then any_live_spec g i c (k - 1)

/// Some slot holds a survivor exactly when fewer slots than all are freed.
let rec dead_count (g: heap) (i: nat) (c: nat{c < n_cls}) (k: nat)
  : Lemma (ensures L.length (dead_list g i c k) <= k /\
                   (any_live g i c k <==> L.length (dead_list g i c k) < k)) (decreases k)
  = if k > 0 then dead_count g i c (k - 1)
#pop-options

let sweep_page (g: heap) (pm: page_map) (i: nat{i < n_pages}) : GTot (heap & page_info) =
  match (entry pm i).kind with
  | Pool c -> if any_live g i c (n_slots c) then pool_swept g pm i c else page_freed g i c
  | _ -> (g, entry pm i)

/// ---------------------------------------------------------------------------
/// Reading the swept heap back
/// ---------------------------------------------------------------------------

/// The two words of a slot lie below every later slot.
let slot_words (i: nat{i < n_pages}) (c: nat{c < n_cls}) (j k: nat)
  : Lemma (requires j < k /\ k <= n_slots c)
          (ensures slot_base i c j + 16 <= slot_base i c k /\
                   slot_base i c (j + 1) <= slot_base i c k)
  = slot_below i c j k;
    slot_base_succ i c j;
    FStar.Math.Lemmas.lemma_mult_le_right (cls c * 8) (j + 1) k

#push-options "--fuel 1"
/// Words outside the slots swept so far are untouched.
let rec sw_out (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat{k <= n_slots c}) (x: hp_addr)
  : Lemma (requires U64.v x + 8 <= page_base i \/ U64.v x >= slot_base i c k)
          (ensures read_word (sw_heap g i c k) x == read_word g x)
          (decreases k)
  = if k = 0 then ()
    else begin
      let j = k - 1 in
      let g1 = sw_heap g i c j in
      let a = slot_hd i c j in
      slot_fits i c j;
      slot_base_succ i c j;
      cls_bounds c;
      sw_out g i c j x;
      if live g i c j then read_write_different g1 a x (colorHeader (read_word g a) White)
      else begin
        read_write_different g1 a x (slot_hdr c);
        read_write_different (write_word g1 a (slot_hdr c)) (slot_link i c j) x (hd_upto g i c j)
      end
    end

/// The header of a swept slot.
let rec sw_hd (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat{k <= n_slots c}) (j: nat{j < k})
  : Lemma (ensures read_word (sw_heap g i c k) (slot_hd i c j) ==
                   (if live g i c j then colorHeader (read_word g (slot_hd i c j)) White else slot_hdr c))
          (decreases k)
  = let m = k - 1 in
    let g1 = sw_heap g i c m in
    let a = slot_hd i c m in
    slot_fits i c m;
    if j = m then begin
      if live g i c m then read_write_same g1 a (colorHeader (read_word g a) White)
      else begin
        read_write_same g1 a (slot_hdr c);
        read_write_different (write_word g1 a (slot_hdr c)) (slot_link i c m) a (hd_upto g i c m)
      end
    end else begin
      sw_hd g i c m j;
      slot_words i c j m;
      if live g i c m then read_write_different g1 a (slot_hd i c j) (colorHeader (read_word g a) White)
      else begin
        read_write_different g1 a (slot_hd i c j) (slot_hdr c);
        read_write_different (write_word g1 a (slot_hdr c)) (slot_link i c m) (slot_hd i c j) (hd_upto g i c m)
      end
    end

/// The link of a freed slot: the free slot before it.
let rec sw_link (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat{k <= n_slots c}) (j: nat{j < k})
  : Lemma (requires not (live g i c j))
          (ensures read_word (sw_heap g i c k) (slot_link i c j) == hd_upto g i c j)
          (decreases k)
  = let m = k - 1 in
    let g1 = sw_heap g i c m in
    let a = slot_hd i c m in
    slot_fits i c m;
    if j = m then
      read_write_same (write_word g1 a (slot_hdr c)) (slot_link i c m) (hd_upto g i c m)
    else begin
      sw_link g i c m j;
      slot_words i c j m;
      if live g i c m then read_write_different g1 a (slot_link i c j) (colorHeader (read_word g a) White)
      else begin
        read_write_different g1 a (slot_link i c j) (slot_hdr c);
        read_write_different (write_word g1 a (slot_hdr c)) (slot_link i c m) (slot_link i c j) (hd_upto g i c m)
      end
    end

/// The rest of a survivor's slot is untouched.
let rec sw_rest (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat{k <= n_slots c}) (j: nat{j < k})
                (x: hp_addr)
  : Lemma (requires live g i c j /\ slot_base i c j < U64.v x /\ U64.v x < slot_base i c (j + 1))
          (ensures read_word (sw_heap g i c k) x == read_word g x)
          (decreases k)
  = let m = k - 1 in
    let g1 = sw_heap g i c m in
    let a = slot_hd i c m in
    slot_fits i c m;
    slot_base_succ i c m;
    if j = m then begin
      sw_out g i c m x;
      read_write_different g1 a x (colorHeader (read_word g a) White)
    end else begin
      sw_rest g i c m j x;
      slot_words i c j m;
      if live g i c m then read_write_different g1 a x (colorHeader (read_word g a) White)
      else begin
        read_write_different g1 a x (slot_hdr c);
        read_write_different (write_word g1 a (slot_hdr c)) (slot_link i c m) x (hd_upto g i c m)
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// The free-slot list
/// ---------------------------------------------------------------------------

#push-options "--fuel 1"
let rec dead_list_mem (g: heap) (i: nat) (c: nat{c < n_cls}) (k: nat) (j: nat)
  : Lemma (ensures L.mem j (dead_list g i c k) <==> (j < k /\ not (live g i c j))) (decreases k)
  = if k > 0 then dead_list_mem g i c (k - 1) j

let rec dead_list_norep (g: heap) (i: nat) (c: nat{c < n_cls}) (k: nat)
  : Lemma (ensures L.noRepeats (dead_list g i c k)) (decreases k)
  = if k > 0 then begin
      dead_list_norep g i c (k - 1);
      dead_list_mem g i c (k - 1) (k - 1)
    end
#pop-options

/// A slot the sweep freed is a free slot of the swept heap.
let sw_free (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (j: nat{j < n_slots c})
  : Lemma (requires not (live g i c j))
          (ensures slot_free (sw_heap g i c (n_slots c)) i c j)
  = sw_hd g i c (n_slots c) j;
    slot_fits i c j;
    cls_bounds c;
    blue_hdr_spec (cls c);
    assert (mk_hp_addr (slot_base i c j) == slot_hd i c j)

/// The list from the head after slot `k - 1` holds the free slots below `k`.
#push-options "--fuel 2"
let rec dead_chain (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat{k <= n_slots c})
  : Lemma (ensures slot_chain (sw_heap g i c (n_slots c)) i c (hd_upto g i c k) (dead_list g i c k))
          (decreases k)
  = let g' = sw_heap g i c (n_slots c) in
    if k = 0 then ()
    else begin
      let j = k - 1 in
      dead_chain g i c j;
      if live g i c j then ()
      else begin
        sw_free g i c j;
        sw_link g i c (n_slots c) j;
        slot_fits i c j;
        assert (mk_hp_addr (slot_obj i c j) == slot_link i c j);
        assert (hdr g' (slot_obj i c j) == hd_upto g i c j)
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// The swept slots
/// ---------------------------------------------------------------------------

let whiten_hdr (h: U64.t)
  : Lemma (getColor (colorHeader h White) == White /\
           getWosize (colorHeader h White) == getWosize h)
  = colorHeader_getColor h White;
    colorHeader_preserves_wosize h White

/// A black slot of a page with the pool shape holds a used slot.
let live_used (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat{k < n_slots c})
  : Lemma (requires pool_shape g i c /\ live g i c k)
          (ensures slot_used g i c k)
  = assert (slot_ok g i c k)

/// The rest of a survivor's slot is unchanged.
let sw_rest_kept (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat{k < n_slots c})
  : Lemma (requires live g i c k)
          (ensures slot_rest_kept g (sw_heap g i c (n_slots c)) i c k)
  = FStar.Classical.forall_intro (FStar.Classical.move_requires (sw_rest g i c (n_slots c) k))

/// A survivor's slot is a used slot of the swept heap, its block made white.
let sw_survivor (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat{k < n_slots c})
  : Lemma (requires pool_shape g i c /\ live g i c k)
          (ensures (let g' = sw_heap g i c (n_slots c) in
                    slot_used g' i c k /\ whitened g g' (slot_hd i c k) /\
                    slot_rest_kept g g' i c k /\
                    color_at g' (slot_base i c k) == White))
  = let g' = sw_heap g i c (n_slots c) in
    let a = slot_hd i c k in
    let s = slot_base i c k in
    live_used g i c k;
    sw_hd g i c (n_slots c) k;
    sw_rest_kept g i c k;
    whiten_hdr (read_word g a);
    assert (mk_hp_addr s == a);
    assert (hdr g' s == colorHeader (hdr g s) White);
    assert (words_at g' s == words_at g s);
    slot_base_succ i c k;
    cls_bounds c;
    if words_at g s < cls c then begin
      let f = s + words_at g s * 8 in
      assert (blue_block g f (cls c - words_at g s));
      assert (hdr g' f == hdr g f)
    end

/// ---------------------------------------------------------------------------
/// The two cases
/// ---------------------------------------------------------------------------

let pool_swept_frame (g: heap) (pm: page_map) (i: nat{i < n_pages}) (c: nat{c < n_cls})
  : Lemma (page_frame g (fst (pool_swept g pm i c)) i /\
           pool_tail_kept g (fst (pool_swept g pm i c)) i c)
  = slots_fill_page i c;
    let aux (x: hp_addr)
      : Lemma (U64.v x + 8 <= page_base i \/ U64.v x >= slots_end i c ==>
               read_word (sw_heap g i c (n_slots c)) x == read_word g x)
      = if U64.v x + 8 <= page_base i || U64.v x >= slots_end i c then sw_out g i c (n_slots c) x
    in
    FStar.Classical.forall_intro aux

let pool_swept_slots (g: heap) (pm: page_map) (i: nat{i < n_pages}) (c: nat{c < n_cls})
  : Lemma (requires pool_shape g i c)
          (ensures (let g' = sw_heap g i c (n_slots c) in
                    (forall (k: nat). k < n_slots c ==>
                       (slot_free g' i c k <==> not (live g i c k)) /\
                       (slot_used g' i c k ==> color_at g' (slot_base i c k) == White) /\
                       slot_ok g' i c k) /\
                    (forall (k: nat{k < n_slots c}). live g i c k ==>
                       slot_used g' i c k /\ whitened g g' (slot_hd i c k) /\
                       slot_rest_kept g g' i c k)))
  = let g' = sw_heap g i c (n_slots c) in
    let aux (k: nat)
      : Lemma (k < n_slots c ==>
                 (slot_free g' i c k <==> not (live g i c k)) /\
                 (slot_used g' i c k ==> color_at g' (slot_base i c k) == White) /\
                 slot_ok g' i c k /\
                 (live g i c k ==> slot_used g' i c k /\ whitened g g' (slot_hd i c k) /\
                                   slot_rest_kept g g' i c k))
      = if k < n_slots c then begin
          if live g i c k then sw_survivor g i c k
          else sw_free g i c k
        end
    in
    FStar.Classical.forall_intro aux

let pool_swept_ok (g: heap) (pm: page_map) (i: nat{i < n_pages}) (c: nat{c < n_cls})
  : Lemma (requires marked_pool_page g pm i c)
          (ensures (let (g', e) = pool_swept g pm i c in
                    let pm' = Seq.upd pm i e in
                    page_frame g g' i /\ e.swept == true /\ e.kind == Pool c /\
                    pool_shape g' i c /\ pool_tail_kept g g' i c /\
                    (forall (k: nat). k < n_slots c /\
                       ~(slot_used g i c k /\ color_at g (slot_base i c k) == Black) ==>
                       slot_free g' i c k) /\
                    (forall (k: nat{k < n_slots c}).
                       slot_used g i c k /\ color_at g (slot_base i c k) == Black ==>
                       slot_used g' i c k /\ whitened g g' (slot_hd i c k) /\
                       slot_rest_kept g g' i c k) /\
                    pool_list_ok g' pm' i /\ pool_white g' pm' i))
  = let (g', e) = pool_swept g pm i c in
    let pm' = Seq.upd pm i e in
    pool_swept_frame g pm i c;
    pool_swept_slots g pm i c;
    slots_fill_page i c;
    if tail_words c > 0 then assert (hdr g' (slots_end i c) == hdr g (slots_end i c));
    assert (pool_shape g' i c);
    dead_chain g i c (n_slots c);
    dead_list_norep g i c (n_slots c);
    FStar.Classical.forall_intro (dead_list_mem g i c (n_slots c));
    assert (entry pm' i == e);
    assert (pool_list_ok g' pm' i);
    assert (pool_white g' pm' i)

let page_freed_ok (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls})
  : Lemma (let (g', e) = page_freed g i c in
           page_frame g g' i /\ e.swept == true /\ e.kind == Free /\ free_page_shape g' i)
  = let g1 = sw_heap g i c (n_slots c) in
    let (g', e) = page_freed g i c in
    cls_bounds 0;
    let a = page_addr i in
    read_write_same g1 a page_hdr;
    blue_hdr_spec page_wsize;
    page_base_mono i (i + 1);
    slots_fill_page i c;
    FStar.Math.Lemmas.distributivity_add_left i 1 page_bytes;
    let aux (x: hp_addr)
      : Lemma (U64.v x + 8 <= page_base i \/ U64.v x >= page_base (i + 1) ==>
               read_word g' x == read_word g x)
      = if U64.v x + 8 <= page_base i || U64.v x >= page_base (i + 1) then begin
          read_write_different g1 a x page_hdr;
          sw_out g i c (n_slots c) x
        end
    in
    FStar.Classical.forall_intro aux

/// ---------------------------------------------------------------------------
/// The theorem
/// ---------------------------------------------------------------------------

/// A black used slot is a survivor in the sweep's sense, and back.
let survivor_iff (g: heap) (pm: page_map) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat)
  : Lemma (requires marked_pool_page g pm i c /\ k < n_slots c)
          (ensures (slot_used g i c k /\ color_at g (slot_base i c k) == Black) <==> live g i c k)
  = if live g i c k then live_used g i c k

let sweep_page_ok_at (g: heap) (pm: page_map) (i: nat{i < n_pages}) (c: nat{c < n_cls})
  : Lemma (requires marked_pool_page g pm i c)
          (ensures (let (g', e) = sweep_page g pm i in sweep_page_ok g pm i c g' e))
  = FStar.Classical.forall_intro (FStar.Classical.move_requires (survivor_iff g pm i c));
    any_live_spec g i c (n_slots c);
    if any_live g i c (n_slots c) then pool_swept_ok g pm i c
    else page_freed_ok g i c

/// **The page sweep meets its specification.**
let sweep_page_correct () : Lemma (sweep_page_meets sweep_page)
  = let aux (g: heap) (pm: page_map) (i: nat{i < n_pages}) (c: nat{c < n_cls})
      : Lemma (marked_pool_page g pm i c ==>
               (let (g', e) = sweep_page g pm i in sweep_page_ok g pm i c g' e))
      = FStar.Classical.move_requires (sweep_page_ok_at g pm i) c
    in
    FStar.Classical.forall_intro_4 aux
