/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.SweepAll - sweeping every page and run once
/// ---------------------------------------------------------------------------
///
/// `sweep_all g st` is the sequential major sweep of plan §1.4: from page 0
/// on, it sweeps each unit (`GC.Spec.Pages.SweepStep`): a pool page with the
/// page sweep, putting it on its class's list if it kept a free slot; a run
/// with the run sweep, linking its listed blocks in front of list 0.  A free
/// page is left alone.  The walk goes from unit to unit by the spans of the
/// map it starts with.
///
/// It starts from the state the mark leaves once the lists are cleared
/// (`sweep_ready`): the pages have their shapes, every page that is not free
/// is unswept, the lists are empty, and no block of a pool page or run is
/// grey.  **`sweep_all_correct`**: it ends with every page swept and
/// `pages_ok`, and each unit holds exactly the mark's survivors, made white
/// (`SweepUnits.unit_ok`).  `no_pointer_to_blue` (L10) needs what the mark
/// guarantees about pointers (`mark_done`).

module GC.Spec.Pages.SweepAll

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
open GC.Spec.Pages.Frame
open GC.Spec.Pages.Cells
open GC.Spec.Pages.Theorems

module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot
module FLs = GC.Spec.FreeLists
module R = GC.Spec.Pages.Replace
module SU = GC.Spec.Pages.SweepUnits
module SS = GC.Spec.Pages.SweepStep
module SP = GC.Spec.Pages.SweepPage
module SR = GC.Spec.Pages.SweepRun
module Mark = GC.Spec.Mark

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The sweep
/// ---------------------------------------------------------------------------

let step (g: heap) (st: pstate) (p: nat{p < n_pages}) : GTot (heap & pstate) =
  if (entry st.pm p).swept then (g, st)
  else match (entry st.pm p).kind with
    | Pool c -> let (g', e) = SP.sweep_page g st.pm p in (g', SS.push_avail st p e)
    | LargeHead n ->
      let (g', pm', fp') = SR.sweep_run g st.pm p (large_head st) in (g', SS.run_state st pm' fp')
    | _ -> (g, st)

#push-options "--fuel 1"
let rec sweep_from (g: heap) (st: pstate) (p: nat)
  : GTot (heap & pstate) (decreases (if p < n_pages then n_pages - p else 0))
  = if p >= n_pages then (g, st)
    else begin
      let k = span st.pm p in
      let (g', st') = step g st p in
      sweep_from g' st' (p + k)
    end
#pop-options

let sweep_all (g: heap) (st: pstate) : GTot (heap & pstate) = sweep_from g st 0

/// ---------------------------------------------------------------------------
/// Where it starts
/// ---------------------------------------------------------------------------

/// The state the mark leaves, with the lists cleared (plan §1.4).
let sweep_ready (g: heap) (st: pstate) : prop =
  shape_ok g st.pm /\
  (forall (j: nat{j < n_pages}). (entry st.pm j).kind =!= Free ==> not (entry st.pm j).swept) /\
  Seq.length st.avail == n_cls /\ (forall (c: nat{c < n_cls}). Seq.index st.avail c == 0UL) /\
  Seq.length st.atail == n_cls /\ (forall (c: nat{c < n_cls}). Seq.index st.atail c == 0UL) /\
  st.large == FLs.fls_empty /\
  (forall (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat).
     (entry st.pm i).kind == Pool c /\ k < n_slots c /\ slot_used g i c k ==>
     color_at g (slot_base i c k) =!= Gray) /\
  (forall (h: nat{h < n_pages}) (a: nat).
     LargeHead? (entry st.pm h).kind /\ run_block g h (run_len (entry st.pm h).kind) a ==>
     color_at g a =!= Gray)

/// What the mark guarantees about pointers.
let mark_done (g: heap) : prop =
  well_formed_heap g /\ Mark.no_pointer_to_blue g /\
  Mark.tri_color_invariant g /\ Mark.noGreyObjects g

/// ---------------------------------------------------------------------------
/// The invariant
/// ---------------------------------------------------------------------------

/// The units before `p` are swept and every later one is as it was.
[@@"opaque_to_smt"]
let inv (g0: heap) (st0: pstate) (g: heap) (st: pstate) (p: nat) : prop =
  p <= n_pages /\ walk_page st0.pm p /\
  shape_ok g st.pm /\ (forall (i: nat{i < n_pages}). page_local g st.pm i) /\
  avail_ok st /\ (exists (cs: list obj_addr). lview g st cs) /\
  (forall (j: nat{j < n_pages}). j >= p ==> entry st.pm j == entry st0.pm j) /\
  (forall (x: hp_addr). U64.v x >= page_base p ==> read_word g x == read_word g0 x) /\
  (forall (j: nat{j < n_pages}). j < p ==> (entry st.pm j).swept == true) /\
  (forall (i: nat{i < n_pages}). i < p /\ walk_page st0.pm i ==>
     walk_page st.pm i /\ i + span st0.pm i <= p /\ SU.unit_ok g0 g i (span st0.pm i))

let inv_elim (g0: heap) (st0: pstate) (g: heap) (st: pstate) (p: nat)
  : Lemma (requires inv g0 st0 g st p)
          (ensures p <= n_pages /\ walk_page st0.pm p /\
                   shape_ok g st.pm /\ (forall (i: nat{i < n_pages}). page_local g st.pm i) /\
                   avail_ok st /\ (exists (cs: list obj_addr). lview g st cs) /\
                   (forall (j: nat{j < n_pages}). j >= p ==> entry st.pm j == entry st0.pm j) /\
                   (forall (x: hp_addr). U64.v x >= page_base p ==> read_word g x == read_word g0 x) /\
                   (forall (j: nat{j < n_pages}). j < p ==> (entry st.pm j).swept == true) /\
                   (forall (i: nat{i < n_pages}). i < p /\ walk_page st0.pm i ==>
                      walk_page st.pm i /\ i + span st0.pm i <= p /\ SU.unit_ok g0 g i (span st0.pm i)))
  = reveal_opaque (`%inv) inv

let inv_intro (g0: heap) (st0: pstate) (g: heap) (st: pstate) (p: nat)
  : Lemma (requires p <= n_pages /\ walk_page st0.pm p /\
                    shape_ok g st.pm /\ (forall (i: nat{i < n_pages}). page_local g st.pm i) /\
                    avail_ok st /\ (exists (cs: list obj_addr). lview g st cs) /\
                    (forall (j: nat{j < n_pages}). j >= p ==> entry st.pm j == entry st0.pm j) /\
                    (forall (x: hp_addr). U64.v x >= page_base p ==> read_word g x == read_word g0 x) /\
                    (forall (j: nat{j < n_pages}). j < p ==> (entry st.pm j).swept == true) /\
                    (forall (i: nat{i < n_pages}). i < p /\ walk_page st0.pm i ==>
                       walk_page st.pm i /\ i + span st0.pm i <= p /\ SU.unit_ok g0 g i (span st0.pm i)))
          (ensures inv g0 st0 g st p)
  = reveal_opaque (`%inv) inv

/// ---------------------------------------------------------------------------
/// The start
/// ---------------------------------------------------------------------------

#push-options "--fuel 1"
let rec empty_chain (pm: page_map) : Lemma (page_chain pm 0UL []) = ()
#pop-options

let init_local (g: heap) (st: pstate) (i: nat{i < n_pages})
  : Lemma (requires sweep_ready g st) (ensures page_local g st.pm i)
  = assert (page_shape g st.pm i);
    assert (map_ok st.pm);
    assert (free_ok st.pm i)

#push-options "--fuel 1"
let init_avail (g: heap) (st: pstate)
  : Lemma (requires sweep_ready g st) (ensures avail_ok st)
  = let aux (c: nat{c < n_cls})
      : Lemma (exists (ps: list nat).
                 page_chain st.pm (Seq.index st.avail c) ps /\ L.noRepeats ps /\
                 (forall (p: nat{p < n_pages}). L.mem p ps <==> has_free_slot st.pm c p) /\
                 Seq.index st.atail c == chain_tail ps)
      = empty_chain st.pm;
        assert (page_chain st.pm (Seq.index st.avail c) []);
        assert (L.noRepeats ([] <: list nat));
        assert (forall (p: nat{p < n_pages}). ~(has_free_slot st.pm c p))
    in
    FStar.Classical.forall_intro aux

let init_lview (g: heap) (st: pstate)
  : Lemma (requires sweep_ready g st) (ensures lview g st [])
  = let heads (i: nat) : Lemma (FLs.fls_head st.large i == 0UL)
      = assert (st.large == FLs.fls_empty)
    in
    FStar.Classical.forall_intro heads;
    let none (y: obj_addr) : Lemma (requires large_listable g st.pm y) (ensures False)
      = eliminate exists (h: nat{h < n_pages}).
          LargeHead? (entry st.pm h).kind /\ (entry st.pm h).swept /\
          page_base h <= U64.v (hd_address y) /\ U64.v (hd_address y) < page_base (h + run_len (entry st.pm h).kind)
        with ()
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires none);
    heap_words_pos ()
#pop-options

let inv_init (g: heap) (st: pstate)
  : Lemma (requires sweep_ready g st) (ensures inv g st g st 0)
  = FStar.Classical.forall_intro (FStar.Classical.move_requires (init_local g st));
    init_avail g st;
    init_lview g st;
    if n_pages > 0 then assert (cont_ok st.pm 0);
    inv_intro g st g st 0

/// ---------------------------------------------------------------------------
/// A step keeps the invariant
/// ---------------------------------------------------------------------------

let page_base_mono_any (i j: nat)
  : Lemma (requires i <= j) (ensures page_base i <= page_base j)
  = FStar.Math.Lemmas.lemma_mult_le_right page_bytes i j

/// The units before `p` lie below page `p`, so a step at `p` keeps their facts.
let units_kept (g0 g g': heap) (st0 st st': pstate) (p q: nat)
  : Lemma (requires p <= q /\ q <= n_pages /\
                    (forall (i: nat{i < n_pages}). i < p /\ walk_page st0.pm i ==>
                       walk_page st.pm i /\ i + span st0.pm i <= p /\ SU.unit_ok g0 g i (span st0.pm i)) /\
                    (forall (x: hp_addr). U64.v x < page_base p ==> read_word g' x == read_word g x) /\
                    (forall (j: nat{j < n_pages}). j < p ==> (entry st'.pm j).kind == (entry st.pm j).kind))
          (ensures forall (i: nat{i < n_pages}). i < p /\ walk_page st0.pm i ==>
                     walk_page st'.pm i /\ i + span st0.pm i <= q /\ SU.unit_ok g0 g' i (span st0.pm i))
  = let aux (i: nat{i < n_pages})
      : Lemma (requires i < p /\ walk_page st0.pm i)
              (ensures walk_page st'.pm i /\ i + span st0.pm i <= q /\ SU.unit_ok g0 g' i (span st0.pm i))
      = let k = span st0.pm i in
        page_base_mono (i + k) p;
        SU.unit_ok_frame g0 g g0 g' i k
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

/// A unit swept from `g` is swept from `g0`, which agrees with `g` on it.
let unit_from (g0 g g': heap) (p k: nat)
  : Lemma (requires SU.unit_ok g g' p k /\
                    (forall (x: hp_addr). U64.v x >= page_base p ==> read_word g x == read_word g0 x))
          (ensures SU.unit_ok g0 g' p k)
  = SU.unit_ok_frame g g' g0 g' p k

/// The unit at `p` joins the units before it.
let units_add (g0 g: heap) (st0 st: pstate) (p: nat{p < n_pages}) (q: nat)
  : Lemma (requires p < q /\
                    (forall (i: nat{i < n_pages}). i < p /\ walk_page st0.pm i ==>
                       walk_page st.pm i /\ i + span st0.pm i <= q /\ SU.unit_ok g0 g i (span st0.pm i)) /\
                    walk_page st.pm p /\ p + span st0.pm p <= q /\ SU.unit_ok g0 g p (span st0.pm p) /\
                    (forall (i: nat{i < n_pages}). p < i /\ i < q ==> ~(walk_page st0.pm i)))
          (ensures forall (i: nat{i < n_pages}). i < q /\ walk_page st0.pm i ==>
                     walk_page st.pm i /\ i + span st0.pm i <= q /\ SU.unit_ok g0 g i (span st0.pm i))
  = ()

let swept_add (pm: page_map) (p q: nat)
  : Lemma (requires (forall (j: nat{j < n_pages}). j < p ==> (entry pm j).swept == true) /\
                    (forall (j: nat{j < n_pages}). p <= j /\ j < q ==> (entry pm j).swept == true))
          (ensures forall (j: nat{j < n_pages}). j < q ==> (entry pm j).swept == true)
  = ()

let entries_from (pm pm0: page_map) (p q: nat)
  : Lemma (requires p <= q /\ (forall (j: nat{j < n_pages}). j >= p ==> entry pm j == entry pm0 j))
          (ensures forall (j: nat{j < n_pages}). j >= q ==> entry pm j == entry pm0 j)
  = ()

let words_from (g g0: heap) (p q: nat)
  : Lemma (requires p <= q /\ (forall (x: hp_addr). U64.v x >= page_base p ==> read_word g x == read_word g0 x))
          (ensures forall (x: hp_addr). U64.v x >= page_base q ==> read_word g x == read_word g0 x)
  = page_base_mono_any p q

let one_swept (pm: page_map) (p: nat{p < n_pages})
  : Lemma (requires (entry pm p).swept == true)
          (ensures forall (j: nat{j < n_pages}). p <= j /\ j < p + 1 ==> (entry pm j).swept == true)
  = ()

let inv_free (g0 g: heap) (st0 st: pstate) (p: nat{p < n_pages})
  : Lemma (requires sweep_ready g0 st0 /\ inv g0 st0 g st p /\ (entry st0.pm p).kind == Free)
          (ensures step g st p == (g, st) /\ inv g0 st0 g st (p + 1))
  = inv_elim g0 st0 g st p;
    assert (map_ok st0.pm /\ free_ok st0.pm p);
    assert ((entry st0.pm p).swept == true);
    assert (entry st.pm p == entry st0.pm p);
    one_swept st.pm p;
    next_walk_page st0.pm p p;
    assert (page_shape g0 st0.pm p);
    page_base_mono p (p + 1);
    SU.free_unit_ok g0 g p;
    units_add g0 g st0 st p (p + 1);
    swept_add st.pm p (p + 1);
    entries_from st.pm st0.pm p (p + 1);
    words_from g g0 p (p + 1);
    inv_intro g0 st0 g st (p + 1)

let marked_pool_at (g0 g: heap) (st0 st: pstate) (p: nat{p < n_pages}) (c: nat{c < n_cls})
  : Lemma (requires sweep_ready g0 st0 /\ inv g0 st0 g st p /\ (entry st0.pm p).kind == Pool c)
          (ensures marked_pool_page g st.pm p c)
  = inv_elim g0 st0 g st p;
    assert (page_shape g st.pm p);
    let aux (k: nat)
      : Lemma (k < n_slots c /\ slot_used g p c k ==> color_at g (slot_base p c k) =!= Gray)
      = if k < n_slots c then begin
          slot_kept g0 g p c k;
          slot_frame g0 g p c k
        end
    in
    FStar.Classical.forall_intro aux

/// What a step at `p` must give for the invariant to move to `q`.
let inv_next (g0 g g': heap) (st0 st st': pstate) (p: nat{p < n_pages}) (q: nat)
  : Lemma (requires inv g0 st0 g st p /\ p < q /\ q <= n_pages /\ walk_page st0.pm q /\
                    q == p + span st0.pm p /\
                    shape_ok g' st'.pm /\ (forall (i: nat{i < n_pages}). page_local g' st'.pm i) /\
                    avail_ok st' /\ (exists (cs: list obj_addr). lview g' st' cs) /\
                    (forall (x: hp_addr). U64.v x < page_base p \/ U64.v x >= page_base q ==>
                       read_word g' x == read_word g x) /\
                    (forall (j: nat{j < n_pages}). j < p ==>
                       (entry st'.pm j).kind == (entry st.pm j).kind /\ (entry st'.pm j).swept == (entry st.pm j).swept) /\
                    (forall (j: nat{j < n_pages}). j >= q ==> entry st'.pm j == entry st.pm j) /\
                    (forall (j: nat{j < n_pages}). p <= j /\ j < q ==> (entry st'.pm j).swept == true) /\
                    walk_page st'.pm p /\
                    SU.unit_ok g g' p (span st0.pm p) /\
                    (forall (i: nat{i < n_pages}). p < i /\ i < q ==> ~(walk_page st0.pm i)))
          (ensures inv g0 st0 g' st' q)
  = inv_elim g0 st0 g st p;
    unit_from g0 g g' p (span st0.pm p);
    units_kept g0 g g' st0 st st' p q;
    units_add g0 g' st0 st' p q;
    swept_add st'.pm p q;
    entries_from st.pm st0.pm p q;
    words_from g g0 p q;
    inv_intro g0 st0 g' st' q

/// The parts of the invariant a step needs.
let inv_parts (g0: heap) (st0: pstate) (g: heap) (st: pstate) (p: nat)
  : Lemma (requires sweep_ready g0 st0 /\ inv g0 st0 g st p)
          (ensures shape_ok g st.pm /\ (forall (i: nat{i < n_pages}). page_local g st.pm i) /\
                   avail_ok st /\ (exists (cs: list obj_addr). lview g st cs) /\
                   map_ok st0.pm /\ p <= n_pages /\ walk_page st0.pm p)
  = inv_elim g0 st0 g st p

let no_between (pm: page_map) (p: nat)
  : Lemma (forall (i: nat{i < n_pages}). p < i /\ i < p + 1 ==> ~(walk_page pm i))
  = ()

let inv_entry (g0: heap) (st0: pstate) (g: heap) (st: pstate) (p: nat{p < n_pages})
  : Lemma (requires inv g0 st0 g st p) (ensures entry st.pm p == entry st0.pm p)
  = inv_elim g0 st0 g st p

let pool_next (g0 g g': heap) (st0 st st': pstate) (p: nat{p < n_pages})
  : Lemma (requires sweep_ready g0 st0 /\ inv g0 st0 g st p /\ p + 1 <= n_pages /\ walk_page st0.pm (p + 1) /\
                    span st0.pm p == 1 /\
                    shape_ok g' st'.pm /\ (forall (i: nat{i < n_pages}). page_local g' st'.pm i) /\
                    avail_ok st' /\ (exists (cs: list obj_addr). lview g' st' cs) /\
                    (forall (x: hp_addr). U64.v x < page_base p \/ U64.v x >= page_base (p + 1) ==>
                       read_word g' x == read_word g x) /\
                    (forall (j: nat{j < n_pages}). j <> p ==> SS.same_but_next (entry st.pm j) (entry st'.pm j)) /\
                    (forall (j: nat{j < n_pages}). j <> p /\ ~(entry st'.pm j == entry st.pm j) ==>
                       (exists (d: nat{d < n_cls}). has_free_slot st.pm d j)) /\
                    (entry st'.pm p).swept == true /\ (entry st'.pm p).kind =!= LargeCont /\
                    SU.unit_ok g g' p 1)
          (ensures inv g0 st0 g' st' (p + 1))
  = inv_elim g0 st0 g st p;
    let ahead (j: nat{j < n_pages}) : Lemma (j >= p + 1 ==> entry st'.pm j == entry st.pm j)
      = if j >= p + 1 then begin
          assert (entry st.pm j == entry st0.pm j);
          assert ((entry st0.pm j).kind =!= Free ==> not (entry st0.pm j).swept);
          assert (forall (d: nat{d < n_cls}). ~(has_free_slot st.pm d j))
        end
    in
    FStar.Classical.forall_intro ahead;
    one_swept st'.pm p;
    no_between st0.pm p;
    inv_next g0 g g' st0 st st' p (p + 1)

let inv_pool (g0 g: heap) (st0 st: pstate) (p: nat{p < n_pages}) (c: nat{c < n_cls})
  : Lemma (requires sweep_ready g0 st0 /\ inv g0 st0 g st p /\ (entry st0.pm p).kind == Pool c)
          (ensures (let (g', st') = step g st p in inv g0 st0 g' st' (p + 1)))
  = marked_pool_at g0 g st0 st p c;
    inv_parts g0 st0 g st p;
    next_walk_page st0.pm p p;
    eliminate exists (cs: list obj_addr). lview g st cs
    with begin
      SS.pool_step g st p c cs;
      let (g', e) = SP.sweep_page g st.pm p in
      let st' = SS.push_avail st p e in
      assert (step g st p == (g', st'));
      pool_next g0 g g' st0 st st' p
    end

let marked_run_at (g0 g: heap) (st0 st: pstate) (p: nat{p < n_pages})
  : Lemma (requires sweep_ready g0 st0 /\ inv g0 st0 g st p /\ LargeHead? (entry st0.pm p).kind)
          (ensures marked_run g st.pm p)
  = inv_elim g0 st0 g st p;
    assert (page_shape g st.pm p);
    let n = run_len (entry st0.pm p).kind in
    let aux (a: nat) : Lemma (run_block g p n a ==> color_at g a =!= Gray)
      = run_block_frame g0 g p n a
    in
    FStar.Classical.forall_intro aux

let run_next (g0 g g': heap) (st0 st st': pstate) (p: nat{p < n_pages}) (n: pos)
  : Lemma (requires inv g0 st0 g st p /\ p + n <= n_pages /\ walk_page st0.pm (p + n) /\
                    span st0.pm p == n /\
                    (forall (i: nat{i < n_pages}). p < i /\ i < p + n ==> ~(walk_page st0.pm i)) /\
                    shape_ok g' st'.pm /\ (forall (i: nat{i < n_pages}). page_local g' st'.pm i) /\
                    avail_ok st' /\ (exists (cs': list obj_addr). lview g' st' cs') /\
                    (forall (x: hp_addr). U64.v x < page_base p \/ U64.v x >= page_base (p + n) ==>
                       read_word g' x == read_word g x) /\
                    (forall (j: nat{j < n_pages}). j < p \/ j >= p + n ==> entry st'.pm j == entry st.pm j) /\
                    (forall (j: nat{j < n_pages}). p <= j /\ j < p + n ==> (entry st'.pm j).swept == true) /\
                    (entry st'.pm p).kind =!= LargeCont /\
                    SU.unit_ok g g' p n)
          (ensures inv g0 st0 g' st' (p + n))
  = inv_next g0 g g' st0 st st' p (p + n)

let inv_run (g0 g: heap) (st0 st: pstate) (p: nat{p < n_pages})
  : Lemma (requires sweep_ready g0 st0 /\ inv g0 st0 g st p /\ LargeHead? (entry st0.pm p).kind)
          (ensures (let (g', st') = step g st p in
                    inv g0 st0 g' st' (p + run_len (entry st0.pm p).kind)))
  = marked_run_at g0 g st0 st p;
    inv_parts g0 st0 g st p;
    let n = run_len (entry st0.pm p).kind in
    inv_entry g0 st0 g st p;
    assert (run_ok st0.pm p);
    next_walk_page st0.pm p p;
    let between (i: nat{i < n_pages})
      : Lemma (p < i /\ i < p + n ==> ~(walk_page st0.pm i))
      = next_walk_page st0.pm p i
    in
    FStar.Classical.forall_intro between;
    eliminate exists (cs: list obj_addr). lview g st cs
    with begin
      SS.run_step g st p n cs;
      let (g', pm', fp') = SR.sweep_run g st.pm p (large_head st) in
      let st' = SS.run_state st pm' fp' in
      assert (step g st p == (g', st'));
      run_next g0 g g' st0 st st' p n
    end

let inv_step (g0 g: heap) (st0 st: pstate) (p: nat{p < n_pages})
  : Lemma (requires sweep_ready g0 st0 /\ inv g0 st0 g st p)
          (ensures (let (g', st') = step g st p in inv g0 st0 g' st' (p + span st.pm p)))
  = inv_elim g0 st0 g st p;
    match (entry st0.pm p).kind with
    | Free -> inv_free g0 g st0 st p
    | Pool c -> inv_pool g0 g st0 st p c
    | LargeHead _ -> inv_run g0 g st0 st p
    | LargeCont -> ()

let inv_bound (g0: heap) (st0: pstate) (g: heap) (st: pstate) (p: nat)
  : Lemma (requires inv g0 st0 g st p) (ensures p <= n_pages)
  = inv_elim g0 st0 g st p

#push-options "--fuel 1"
let rec sweep_from_inv (g0 g: heap) (st0 st: pstate) (p: nat)
  : Lemma (requires sweep_ready g0 st0 /\ inv g0 st0 g st p)
          (ensures (let (g', st') = sweep_from g st p in inv g0 st0 g' st' n_pages))
          (decreases (if p < n_pages then n_pages - p else 0))
  = inv_bound g0 st0 g st p;
    if p >= n_pages then ()
    else begin
      inv_step g0 g st0 st p;
      let (g', st') = step g st p in
      sweep_from_inv g0 g' st0 st' (p + span st.pm p)
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Every block that is not free is a survivor
/// ---------------------------------------------------------------------------

/// A block that is not free lies in the pages, not in the heap's tail.
let not_tail (g: heap) (pm: page_map) (h: nat)
  : Lemma (requires shape_ok g pm /\ steps_to g (U64.v zero_addr) h /\ h + 8 < heap_size /\
                    color_at g h =!= Blue)
          (ensures h < pages_end)
  = pages_end_bound ();
    page_base_aligned n_pages;
    if h >= pages_end then begin
      if heap_size - pages_end < 16 then SS.aligned_lt pages_end heap_size
      else begin
        walk_pages_reached g pm n_pages;
        R.steps_to_det g (U64.v zero_addr) pages_end h;
        if h > pages_end then begin
          steps_to_refl g pages_end;
          R.block_before g pages_end pages_end h;
          FStar.Math.Lemmas.lemma_div_exact (heap_size - pages_end) 8
        end
      end
    end

/// The unit a block that is not free lies in.
let in_unit (g: heap) (pm0 pm: page_map) (h: nat)
  : Lemma (requires shape_ok g pm /\ map_ok pm0 /\
                    (forall (i: nat{i < n_pages}). walk_page pm0 i ==> walk_page pm i) /\
                    steps_to g (U64.v zero_addr) h /\ h + 8 < heap_size /\ color_at g h =!= Blue)
          (ensures exists (i: nat{i < n_pages}).
                     walk_page pm0 i /\ page_base i <= h /\ h < page_base (i + span pm0 i) /\
                     steps_to g (page_base i) h)
  = not_tail g pm h;
    steps_to_le g (U64.v zero_addr) h;
    page_of_spec h;
    let j = page_of h in
    let found (i: nat{i < n_pages})
      : Lemma (requires walk_page pm0 i /\ page_base i <= h /\ h < page_base (i + span pm0 i))
              (ensures steps_to g (page_base i) h)
      = walk_pages_reached g pm i;
        R.steps_to_det g (U64.v zero_addr) (page_base i) h
    in
    if walk_page pm0 j then found j
    else begin
      assert (cont_ok pm0 j);
      eliminate exists (u: nat{u < n_pages}). u < j /\ in_run pm0 u j
      with begin
        page_base_mono u j;
        page_base_mono (j + 1) (u + run_len (entry pm0 u).kind);
        found u
      end
    end

/// The invariant at the end, and what it gives.
let end_facts (g0 g: heap) (st0 st: pstate)
  : Lemma (requires sweep_ready g0 st0 /\ inv g0 st0 g st n_pages)
          (ensures shape_ok g st.pm /\ map_ok st0.pm /\
                   (forall (i: nat{i < n_pages}). walk_page st0.pm i ==> walk_page st.pm i) /\
                   (forall (i: nat{i < n_pages}). walk_page st0.pm i ==>
                      SU.unit_ok g0 g i (span st0.pm i)))
  = inv_elim g0 st0 g st n_pages

/// A block of the swept heap that is not free is a survivor of the mark,
/// made white.
let survivor_at (g0 g: heap) (st0 st: pstate) (h: nat)
  : Lemma (requires sweep_ready g0 st0 /\ inv g0 st0 g st n_pages /\
                    steps_to g (U64.v zero_addr) h /\ h + 8 < heap_size /\ color_at g h =!= Blue)
          (ensures steps_to g0 (U64.v zero_addr) h /\ color_at g0 h == Black /\ whitened_at g0 g h)
  = end_facts g0 g st0 st;
    in_unit g st0.pm st.pm h;
    eliminate exists (i: nat{i < n_pages}).
      walk_page st0.pm i /\ page_base i <= h /\ h < page_base (i + span st0.pm i) /\
      steps_to g (page_base i) h
    with begin
      walk_pages_reached g0 st0.pm i;
      steps_to_trans g0 (U64.v zero_addr) (page_base i) h
    end

/// A black block of the marked heap is a block of the swept heap, made white.
let black_kept (g0 g: heap) (st0 st: pstate) (h: nat)
  : Lemma (requires sweep_ready g0 st0 /\ inv g0 st0 g st n_pages /\
                    steps_to g0 (U64.v zero_addr) h /\ h + 8 < heap_size /\ color_at g0 h == Black)
          (ensures steps_to g (U64.v zero_addr) h /\ whitened_at g0 g h)
  = end_facts g0 g st0 st;
    in_unit g0 st0.pm st0.pm h;
    eliminate exists (i: nat{i < n_pages}).
      walk_page st0.pm i /\ page_base i <= h /\ h < page_base (i + span st0.pm i) /\
      steps_to g0 (page_base i) h
    with begin
      walk_pages_reached g st.pm i;
      steps_to_trans g (U64.v zero_addr) (page_base i) h
    end

/// ---------------------------------------------------------------------------
/// No pointer to a free block (L10)
/// ---------------------------------------------------------------------------

/// Making a header white keeps its tag.
let whiten_tag (x: obj_addr) (g: heap)
  : Lemma (getTag (colorHeader (read_word g (hd_address x)) White) == getTag (read_word g (hd_address x)))
  = let v = colorHeader (read_word g (hd_address x)) White in
    makeWhite_eq x g;
    makeWhite_spec x g;
    color_preserves_tag x g White;
    tag_of_object_spec x g;
    tag_of_object_spec x (makeWhite x g);
    read_write_same g (hd_address x) v

/// An object of the swept heap that is not free is the same object of the
/// marked heap, black there: same size, tag and fields.
let obj_survivor (g0 g: heap) (st0 st: pstate) (x: obj_addr)
  : Lemma (requires sweep_ready g0 st0 /\ inv g0 st0 g st n_pages /\
                    Seq.mem x (objects zero_addr g) /\ ~(is_blue x g))
          (ensures Seq.mem x (objects zero_addr g0) /\ is_black x g0 /\
                   wosize_of_object x g == wosize_of_object x g0 /\
                   tag_of_object x g == tag_of_object x g0 /\
                   (forall (b: hp_addr). U64.v x <= U64.v b /\
                      U64.v b < U64.v x + U64.v (wosize_of_object x g0) * 8 ==>
                      read_word g b == read_word g0 b))
  = let h = U64.v x - 8 in
    hd_address_spec x;
    R.hdr_obj g x;
    R.hdr_obj g0 x;
    is_blue_iff x g;
    R.obj_iff g x;
    survivor_at g0 g st0 st h;
    colorHeader_preserves_wosize (hdr g0 h) White;
    whiten_tag x g0;
    R.obj_iff g0 x;
    is_black_iff x g0;
    wosize_of_object_spec x g;
    wosize_of_object_spec x g0;
    tag_of_object_spec x g;
    tag_of_object_spec x g0

/// A pointer field of an object of the marked heap that is not free, as
/// `GC.Spec.Pages.Replace.old_target`, also giving the edge.
let old_edge (g: heap) (src: obj_addr) (j: nat) (v: obj_addr)
  : Lemma (requires well_formed_heap g /\ Mark.no_pointer_to_blue g /\
                    Seq.mem src (objects zero_addr g) /\ fields_constrained g src /\
                    R.field_at g src j /\ read_word g (R.field_addr src j) == (v <: U64.t) /\
                    is_pointer (v <: U64.t))
          (ensures points_to g src v /\
                   Seq.mem (resolve_object v g) (objects zero_addr g) /\
                   infix_addr_wf g (objects zero_addr g) v /\
                   ~(is_blue (resolve_object v g) g))
  = wosize_of_object_bound src g;
    FStar.Math.Lemmas.pow2_lt_compat 61 54;
    FStar.Math.Lemmas.pow2_lt_compat 64 61;
    let k = U64.uint_to_t j in
    assert (U64.v (U64.add_mod src (U64.mul_mod k mword)) == U64.v src + j * 8);
    assert (U64.add_mod src (U64.mul_mod k mword) == R.field_addr src j);
    hd_address_spec src;
    hd_address_spec v;
    assert (is_pointer_to (read_word g (R.field_addr src j)) v);
    wf_object_size_bound g src;
    wosize_of_object_bound src g;
    field_read_implies_exists_pointing g src (wosize_of_object src g) k v;
    wf_field_target_in_objects g src v;
    wf_field_target_infix_wf g src v;
    is_blue_iff src g;
    assert (points_to g src v)

/// The mark leaves every pointer of a black object on a black object.
let target_black (g: heap) (src: obj_addr) (j: nat) (v: obj_addr)
  : Lemma (requires mark_done g /\ Seq.mem src (objects zero_addr g) /\ is_black src g /\
                    ~(is_no_scan src g) /\
                    R.field_at g src j /\ read_word g (R.field_addr src j) == (v <: U64.t) /\
                    is_pointer (v <: U64.t))
          (ensures Seq.mem (resolve_object v g) (objects zero_addr g) /\
                   infix_addr_wf g (objects zero_addr g) v /\
                   is_black (resolve_object v g) g)
  = Mark.colors_exclusive src g;
    old_edge g src j v;
    let r = resolve_object v g in
    Mark.color_exhaustive r g

/// Where an infix pointer's header lies: inside its closure's fields.
let infix_inside (g: heap) (v: obj_addr)
  : Lemma (requires is_infix v g /\ infix_addr_wf g (objects zero_addr g) v)
          (ensures (let r = resolve_object v g in
                    U64.v r <= U64.v (hd_address v) /\
                    U64.v (hd_address v) < U64.v r + U64.v (wosize_of_object r g) * 8))
  = infix_addr_wf_elim g (objects zero_addr g) v;
    parent_closure_addr_nat_spec v g;
    resolve_infix_spec v g;
    hd_address_spec v

/// The target of a survivor's pointer resolves to the same object, which
/// survived too, white.
let target_after (g0 g: heap) (st0 st: pstate) (v: obj_addr)
  : Lemma (requires sweep_ready g0 st0 /\ inv g0 st0 g st n_pages /\
                    Seq.mem (resolve_object v g0) (objects zero_addr g0) /\
                    infix_addr_wf g0 (objects zero_addr g0) v /\
                    is_black (resolve_object v g0) g0)
          (ensures resolve_object v g == resolve_object v g0 /\
                   ~(is_blue (resolve_object v g) g))
  = let r = resolve_object v g0 in
    let hr = U64.v r - 8 in
    hd_address_spec r;
    R.hdr_obj g0 r;
    R.obj_iff g0 r;
    is_black_iff r g0;
    black_kept g0 g st0 st hr;
    R.hdr_obj g r;
    colorHeader_getColor (hdr g0 hr) White;
    is_blue_iff r g;
    if is_infix v g0 then begin
      infix_inside g0 v;
      hd_address_spec v;
      wosize_of_object_spec r g0;
      assert (read_word g (hd_address v) == read_word g0 (hd_address v));
      resolve_object_locality v g0 g
    end else begin
      resolve_non_infix v g0;
      whiten_tag v g0;
      R.hdr_obj g v;
      R.hdr_obj g0 v;
      tag_of_object_spec v g;
      tag_of_object_spec v g0;
      is_infix_spec v g;
      is_infix_spec v g0;
      resolve_non_infix v g
    end

/// A pointer field of an object of the swept heap that is not free.
let field_after (g0 g: heap) (st0 st: pstate) (src dst: obj_addr) (j: nat)
  : Lemma (requires sweep_ready g0 st0 /\ mark_done g0 /\ inv g0 st0 g st n_pages /\
                    Seq.mem src (objects zero_addr g) /\ ~(is_blue src g) /\ fields_constrained g src /\
                    j < U64.v (wosize_of_object src g) /\ U64.v src + j * 8 + 8 <= heap_size /\
                    is_pointer_to (read_word g (U64.uint_to_t (U64.v src + j * 8))) dst)
          (ensures ~(is_blue (resolve_object dst g) g))
  = obj_survivor g0 g st0 st src;
    let fa = R.field_addr src j in
    assert (U64.uint_to_t (U64.v src + j * 8) == fa);
    let v = read_word g fa in
    hd_address_spec dst;
    hd_address_spec v;
    assert (v == (dst <: U64.t));
    assert (read_word g0 fa == v);
    is_no_scan_spec src g;
    is_no_scan_spec src g0;
    target_black g0 src j dst;
    target_after g0 g st0 st dst

let no_blue_after (g0 g: heap) (st0 st: pstate)
  : Lemma (requires sweep_ready g0 st0 /\ mark_done g0 /\ inv g0 st0 g st n_pages)
          (ensures Mark.no_pointer_to_blue g)
  = R.part1_always g;
    Mark.no_pointer_to_blue_intro_from_fields g (field_after g0 g st0 st)

/// ---------------------------------------------------------------------------
/// The theorem
/// ---------------------------------------------------------------------------

/// **The whole sweep is correct.**  From the state the mark leaves, it ends
/// with every page swept and `pages_ok`; every unit holds exactly the
/// mark's survivors, made white.
let sweep_all_correct (g: heap) (st: pstate)
  : Lemma (requires sweep_ready g st /\ mark_done g)
          (ensures (let (g', st') = sweep_all g st in
                    pages_ok g' st' /\
                    (forall (j: nat{j < n_pages}). (entry st'.pm j).swept == true) /\
                    (forall (i: nat{i < n_pages}). walk_page st.pm i ==> SU.unit_ok g g' i (span st.pm i))))
  = inv_init g st;
    sweep_from_inv g g st st 0;
    let (g', st') = sweep_all g st in
    inv_elim g st g' st' n_pages;
    no_blue_after g g' st st';
    eliminate exists (cs: list obj_addr). lview g' st' cs
    with lview_large_ok g' st' cs;
    GC.Spec.Pages.Step.pages_ok_intro g' st'
