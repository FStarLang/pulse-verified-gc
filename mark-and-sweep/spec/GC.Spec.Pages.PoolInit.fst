/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.PoolInit - a fresh pool page: every slot free and listed
/// ---------------------------------------------------------------------------
///
/// `pool_init g i c` lays page `i` out as a page of class `c` with every slot
/// free: a blue header on every slot, each slot's first field linking to the
/// next slot, the last to 0, and a blue filler on the page tail.  It writes
/// only inside page `i`.
///
/// `pool_init_ok` shows that the result has the pool shape (L3) and that its
/// free-slot list holds exactly the free slots (L4).  This is the
/// non-vacuity check for the pool clauses of `pages_ok`, and the step the
/// allocator takes when it turns a free page into a pool page.

module GC.Spec.Pages.PoolInit

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

module U64 = FStar.UInt64
module L = FStar.List.Tot

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// Slot `k` of a page lies inside the heap, with room for its link.
let slot_fits (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat{k < n_slots c})
  : Lemma (slot_base i c k % 8 == 0 /\ slot_base i c k + 16 <= slots_end i c /\
           slots_end i c <= page_base (i + 1) /\ page_base (i + 1) <= heap_size /\
           page_base i <= slot_base i c k)
  = slot_base_aligned i c k;
    slot_in_page i c k;
    slots_fill_page i c;
    cls_bounds c;
    page_base_mono (i + 1) n_pages

let slot_hd (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat{k < n_slots c})
  : a: hp_addr{U64.v a == slot_base i c k} =
  slot_fits i c k; mk_hp_addr (slot_base i c k)

let slot_link (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat{k < n_slots c})
  : a: hp_addr{U64.v a == slot_obj i c k} =
  slot_fits i c k; mk_hp_addr (slot_obj i c k)

/// The link stored in slot `k`: the next slot's entry, or 0 after the last.
let link_val (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat{k < n_slots c}) : U64.t =
  if k + 1 < n_slots c then U64.uint_to_t (U64.v (slot_link i c (k + 1))) else 0UL

let slot_hdr (c: nat{c < n_cls}) : U64.t = cls_bounds c; blue_hdr (cls c)

/// Writes slots `0 .. k-1`.
let rec write_slots (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat{k <= n_slots c})
  : GTot heap (decreases k)
  = if k = 0 then g
    else
      let g1 = write_slots g i c (k - 1) in
      let g2 = write_word g1 (slot_hd i c (k - 1)) (slot_hdr c) in
      write_word g2 (slot_link i c (k - 1)) (link_val i c (k - 1))

let tail_filler_hdr (c: nat{c < n_cls}) : U64.t =
  if tail_words c > 0 then (cls_bounds c; blue_hdr (tail_words c)) else 0UL

let pool_init (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) : GTot heap =
  let g1 = write_slots g i c (n_slots c) in
  if tail_words c > 0 then begin
    slots_fill_page i c;
    page_base_mono (i + 1) n_pages;
    slot_base_aligned i c (n_slots c);
    write_word g1 (mk_hp_addr (slots_end i c)) (tail_filler_hdr c)
  end
  else g1

/// ---------------------------------------------------------------------------
/// Reading it back
/// ---------------------------------------------------------------------------

/// Two words of slots `j < k` lie below slot `k`.
let slot_below (i: nat{i < n_pages}) (c: nat{c < n_cls}) (j k: nat)
  : Lemma (requires j < k /\ k <= n_slots c)
          (ensures slot_base i c j + 16 <= slot_base i c k)
  = cls_bounds c;
    slot_base_succ i c j;
    FStar.Math.Lemmas.lemma_mult_le_right (cls c * 8) (j + 1) k

#push-options "--fuel 1"
let rec write_slots_read (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls})
                         (k: nat{k <= n_slots c}) (j: nat{j < k})
  : Lemma (ensures read_word (write_slots g i c k) (slot_hd i c j) == slot_hdr c /\
                   read_word (write_slots g i c k) (slot_link i c j) == link_val i c j)
          (decreases k)
  = let g1 = write_slots g i c (k - 1) in
    let g2 = write_word g1 (slot_hd i c (k - 1)) (slot_hdr c) in
    let v = link_val i c (k - 1) in
    if j = k - 1 then begin
      read_write_same g2 (slot_link i c j) v;
      read_write_same g1 (slot_hd i c j) (slot_hdr c);
      read_write_different g2 (slot_link i c j) (slot_hd i c j) v
    end else begin
      write_slots_read g i c (k - 1) j;
      slot_below i c j (k - 1);
      read_write_different g1 (slot_hd i c (k - 1)) (slot_hd i c j) (slot_hdr c);
      read_write_different g1 (slot_hd i c (k - 1)) (slot_link i c j) (slot_hdr c);
      read_write_different g2 (slot_link i c (k - 1)) (slot_hd i c j) v;
      read_write_different g2 (slot_link i c (k - 1)) (slot_link i c j) v
    end

/// Words outside the slots written are untouched.
let rec write_slots_other (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls})
                          (k: nat{k <= n_slots c}) (a: hp_addr)
  : Lemma (requires U64.v a + 8 <= page_base i \/ U64.v a >= slot_base i c k)
          (ensures read_word (write_slots g i c k) a == read_word g a)
          (decreases k)
  = if k = 0 then ()
    else begin
      let g1 = write_slots g i c (k - 1) in
      let g2 = write_word g1 (slot_hd i c (k - 1)) (slot_hdr c) in
      slot_fits i c (k - 1);
      slot_base_succ i c (k - 1);
      cls_bounds c;
      write_slots_other g i c (k - 1) a;
      read_write_different g1 (slot_hd i c (k - 1)) a (slot_hdr c);
      read_write_different g2 (slot_link i c (k - 1)) a (link_val i c (k - 1))
    end
#pop-options

let pool_init_slot (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat{k < n_slots c})
  : Lemma (read_word (pool_init g i c) (slot_hd i c k) == slot_hdr c /\
           read_word (pool_init g i c) (slot_link i c k) == link_val i c k)
  = write_slots_read g i c (n_slots c) k;
    if tail_words c > 0 then begin
      slots_fill_page i c;
      page_base_mono (i + 1) n_pages;
      slot_base_aligned i c (n_slots c);
      slot_below i c k (n_slots c);
      let t = mk_hp_addr (slots_end i c) in
      read_write_different (write_slots g i c (n_slots c)) t (slot_hd i c k) (tail_filler_hdr c);
      read_write_different (write_slots g i c (n_slots c)) t (slot_link i c k) (tail_filler_hdr c)
    end

/// ---------------------------------------------------------------------------
/// Shape and list
/// ---------------------------------------------------------------------------

let pool_init_free (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat{k < n_slots c})
  : Lemma (slot_free (pool_init g i c) i c k)
  = pool_init_slot g i c k;
    slot_fits i c k;
    cls_bounds c;
    blue_hdr_spec (cls c);
    assert (mk_hp_addr (slot_base i c k) == slot_hd i c k)

let pool_init_shape (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls})
  : Lemma (pool_shape (pool_init g i c) i c)
  = let aux (k: nat) : Lemma (k < n_slots c ==> slot_ok (pool_init g i c) i c k)
      = if k < n_slots c then pool_init_free g i c k
    in
    FStar.Classical.forall_intro aux;
    if tail_words c > 0 then begin
      slots_fill_page i c;
      page_base_mono (i + 1) n_pages;
      slot_base_aligned i c (n_slots c);
      cls_bounds c;
      let t = mk_hp_addr (slots_end i c) in
      read_write_same (write_slots g i c (n_slots c)) t (tail_filler_hdr c);
      blue_hdr_spec (tail_words c)
    end

#push-options "--fuel 1"
/// The slots `k, k+1, ..., n-1`.
let rec range (k n: nat) : Tot (list nat) (decreases (if k < n then n - k else 0)) =
  if k < n then k :: range (k + 1) n else []

let rec range_mem (k n j: nat)
  : Lemma (ensures L.mem j (range k n) <==> (k <= j /\ j < n))
          (decreases (if k < n then n - k else 0))
  = if k < n then range_mem (k + 1) n j

let rec range_props (k n: nat)
  : Lemma (ensures L.noRepeats (range k n) /\ L.length (range k n) == (if k < n then n - k else 0))
          (decreases (if k < n then n - k else 0))
  = if k < n then begin range_props (k + 1) n; range_mem (k + 1) n k end

/// The list from slot `k`'s entry holds slots `k .. n_slots - 1`.
#push-options "--fuel 2"
let rec pool_init_chain (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat{k < n_slots c})
  : Lemma (ensures slot_chain (pool_init g i c) i c (U64.uint_to_t (slot_obj i c k)) (range k (n_slots c)))
          (decreases (n_slots c - k))
  = let g' = pool_init g i c in
    slot_fits i c k;
    pool_init_free g i c k;
    pool_init_slot g i c k;
    assert (mk_hp_addr (slot_obj i c k) == slot_link i c k);
    if k + 1 < n_slots c then pool_init_chain g i c (k + 1)
    else assert (range (k + 1) (n_slots c) == [])
#pop-options
#pop-options

/// The page-map entry of a fresh pool page.
let pool_entry (i: nat{i < n_pages}) (c: nat{c < n_cls}) : page_info =
  slot_fits i c 0;
  { kind = Pool c; swept = true; free_head = U64.uint_to_t (slot_obj i c 0);
    nfree = n_slots c; next = 0UL }

/// **Non-vacuity of L3 and L4.**  A fresh pool page has the pool shape, and
/// its list holds exactly its free slots, all of them.  Nothing outside the
/// page changes.
let pool_init_ok (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls})
  : Lemma (let g' = pool_init g i c in
           let e = pool_entry i c in
           pool_shape g' i c /\
           (exists (ks: list nat).
              slot_chain g' i c e.free_head ks /\ L.noRepeats ks /\
              (forall (k: nat). k < n_slots c ==> (L.mem k ks <==> slot_free g' i c k)) /\
              e.nfree == L.length ks) /\
           (forall (a: hp_addr). U64.v a + 8 <= page_base i \/ U64.v a >= page_base (i + 1) ==>
              read_word g' a == read_word g a))
  = let g' = pool_init g i c in
    pool_init_shape g i c;
    pool_init_chain g i c 0;
    range_props 0 (n_slots c);
    let mem_iff (k: nat) : Lemma (k < n_slots c ==> (L.mem k (range 0 (n_slots c)) <==> slot_free g' i c k))
      = range_mem 0 (n_slots c) k;
        if k < n_slots c then pool_init_free g i c k
    in
    FStar.Classical.forall_intro mem_iff;
    let frame (a: hp_addr)
      : Lemma (U64.v a + 8 <= page_base i \/ U64.v a >= page_base (i + 1) ==> read_word g' a == read_word g a)
      = if U64.v a + 8 <= page_base i || U64.v a >= page_base (i + 1) then begin
          slots_fill_page i c;
          write_slots_other g i c (n_slots c) a;
          if tail_words c > 0 then begin
            page_base_mono (i + 1) n_pages;
            slot_base_aligned i c (n_slots c);
            let t = mk_hp_addr (slots_end i c) in
            read_write_different (write_slots g i c (n_slots c)) t a (tail_filler_hdr c)
          end
        end
    in
    FStar.Classical.forall_intro frame
