/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.SweepRange - sweeping the units of a range of pages
/// ---------------------------------------------------------------------------
///
/// The parallel sweep (docs/pages-parallel-gc-design.md §2) cuts the pages
/// into chunks and sweeps each one on its own.  This module gives the sweep
/// of a range and the two facts about it that the chunks rest on:
///
///   - `crange g st ol p hi` is `SweepAll.sweep_from` stopped at page `hi`:
///     it sweeps the units from page `p` on, as `SweepAll.step` does, until
///     it reaches `hi`.  Beside the heap and the state it returns the range's
///     *open link* `ol`: the link field of the last block listed by the first
///     run that lists a block while the large list is empty
///     (`open_of`, `ostep`).  A chunk swept from empty lists leaves that link
///     holding 0; the join later sets it to the head of the rest of list 0.
///   - `crange_from` and `crange_trans`: sweeping to `hi` and then on is
///     sweeping on, when the walk from `p` lands on `hi` (`wreach`).
///   - **The frame and locality of a range** (the chunk versions of
///     `SweepOrder.unit_frame` and `unit_local`), in the form the join needs:
///     a heap write outside the range commutes with sweeping it
///     (`crange_wr`), and so does setting the class-list link of a page below
///     the range (`crange_sn`).  Both follow from the units' frame and
///     locality, unit by unit.

module GC.Spec.Pages.SweepRange

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Lib.Header
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Inv
open GC.Spec.Pages.Blk
open GC.Spec.Pages.RunList

module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot
module FLs = GC.Spec.FreeLists
module B = GC.Spec.Pages.Blocks
module SP = GC.Spec.Pages.SweepPage
module SR = GC.Spec.Pages.SweepRun
module SS = GC.Spec.Pages.SweepStep
module SA = GC.Spec.Pages.SweepAll
module SO = GC.Spec.Pages.SweepOrder
module Fr = GC.Spec.Pages.Frame
module Ce = GC.Spec.Pages.Cells
module RM = GC.Spec.Pages.RunMap
module HE = GC.Gen.HeapExtensional

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The open link
/// ---------------------------------------------------------------------------

/// The link field of the last block a run's layout lists, 0 if it lists none.
#push-options "--fuel 1"
let rec open_of (bs: list blk) : Tot U64.t (decreases bs) =
  match bs with
  | [] -> 0UL
  | b :: bs' ->
    let o = open_of bs' in
    if o <> 0UL then o else if SR.listable b then (SR.obj_at b <: U64.t) else 0UL
#pop-options

/// The layout the sweep gives the run of `n` pages at page `p`.
let run_fs (g: heap) (p n: nat) : list blk = fin g (page_base p) (page_base (p + n))

/// The open link after the unit at `p`: set by the first run that lists a
/// block while list 0 is empty.
let ostep (g: heap) (st: pstate) (ol: U64.t) (p: nat{p < n_pages}) : U64.t =
  if (entry st.pm p).swept then ol
  else match (entry st.pm p).kind with
    | LargeHead n ->
      if Ce.large_head st = 0UL && open_of (run_fs g p n) <> 0UL then open_of (run_fs g p n) else ol
    | _ -> ol

/// ---------------------------------------------------------------------------
/// The sweep of a range
/// ---------------------------------------------------------------------------

let cg (t: heap & pstate & U64.t) : heap = match t with (g, _, _) -> g
let cs (t: heap & pstate & U64.t) : pstate = match t with (_, st, _) -> st
let co (t: heap & pstate & U64.t) : U64.t = match t with (_, _, ol) -> ol

#push-options "--fuel 1"
let rec crange (g: heap) (st: pstate) (ol: U64.t) (p hi: nat)
  : GTot (heap & pstate & U64.t) (decreases (if p < hi then hi - p else 0))
  = if p >= hi || p >= n_pages then (g, st, ol)
    else begin
      let ol' = ostep g st ol p in
      let (g', st') = SA.step g st p in
      crange g' st' ol' (p + span st.pm p) hi
    end

let crange_stop (g: heap) (st: pstate) (ol: U64.t) (p hi: nat)
  : Lemma (requires p >= hi \/ p >= n_pages) (ensures crange g st ol p hi == (g, st, ol))
  = ()

let crange_step (g: heap) (st: pstate) (ol: U64.t) (p hi: nat)
  : Lemma (requires p < hi /\ p < n_pages)
          (ensures crange g st ol p hi ==
                   crange (fst (SA.step g st p)) (snd (SA.step g st p)) (ostep g st ol p)
                          (p + span st.pm p) hi)
  = ()

let sweep_from_step (g: heap) (st: pstate) (p: nat)
  : Lemma (requires p < n_pages)
          (ensures SA.sweep_from g st p ==
                   SA.sweep_from (fst (SA.step g st p)) (snd (SA.step g st p)) (p + span st.pm p))
  = ()

let sweep_from_end (g: heap) (st: pstate) (p: nat)
  : Lemma (requires p >= n_pages) (ensures SA.sweep_from g st p == (g, st))
  = ()
#pop-options

/// The walk over the units from page `p` lands on page `hi`.
#push-options "--fuel 1"
let rec wreach (pm: page_map) (p hi: nat) : Tot bool (decreases (if p < hi then hi - p else 0)) =
  p = hi || (p < hi && p < n_pages && wreach pm (p + span pm p) hi)
#pop-options

/// The pages from `p` on have the same kinds in two maps.
let kinds_from (pm1 pm2: page_map) (p: nat) : prop =
  forall (j: nat{j < n_pages}). j >= p ==> (entry pm1 j).kind == (entry pm2 j).kind

#push-options "--fuel 1"
let rec wreach_kinds (pm1 pm2: page_map) (p hi: nat)
  : Lemma (requires kinds_from pm1 pm2 p)
          (ensures wreach pm1 p hi == wreach pm2 p hi)
          (decreases (if p < hi then hi - p else 0))
  = if p < hi && p < n_pages then wreach_kinds pm1 pm2 (p + span pm1 p) hi

let wreach_le (pm: page_map) (p hi: nat)
  : Lemma (requires wreach pm p hi) (ensures p <= hi)
  = ()

let wreach_next (pm: page_map) (p hi: nat)
  : Lemma (requires wreach pm p hi /\ p <> hi)
          (ensures p < hi /\ p < n_pages /\ wreach pm (p + span pm p) hi)
  = ()

let wreach_bound (pm: page_map) (p hi: nat)
  : Lemma (requires wreach pm p hi /\ p < n_pages) (ensures p + span pm p <= hi \/ p = hi)
          (decreases (if p < hi then hi - p else 0))
  = if p <> hi then wreach_le pm (p + span pm p) hi

#pop-options

/// A walk page reaches every later walk page.
#push-options "--fuel 2"
let rec walk_reach (pm: page_map) (p q: nat)
  : Lemma (requires map_ok pm /\ p <= q /\ q <= n_pages /\ walk_page pm p /\ walk_page pm q)
          (ensures wreach pm p q)
          (decreases (q - p))
  = if p = q then ()
    else begin
      next_walk_page pm p q;
      let p' = p + span pm p in
      if p' < q then begin
        next_walk_page pm p p';
        walk_reach pm p' q
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// What a step changes in the map
/// ---------------------------------------------------------------------------

/// A step changes no page's kind outside its unit.
let step_kinds (g: heap) (st: pstate) (p: nat{p < n_pages}) (j: nat{j < n_pages})
  : Lemma (requires j < p \/ j >= p + span st.pm p)
          (ensures (entry (snd (SA.step g st p)).pm j).kind == (entry st.pm j).kind)
  = if (entry st.pm p).swept then ()
    else match (entry st.pm p).kind with
      | Pool c ->
        let e = snd (SP.sweep_page g st.pm p) in
        SS.push_entry st p e;
        SS.push_frame st p e
      | LargeHead n -> RM.new_map_entry st.pm (run_fs g p n) p n j
      | _ -> ()

let step_kinds_from (g: heap) (st: pstate) (p: nat{p < n_pages})
  : Lemma (kinds_from (snd (SA.step g st p)).pm st.pm (p + span st.pm p))
  = FStar.Classical.forall_intro (FStar.Classical.move_requires (step_kinds g st p))

/// ---------------------------------------------------------------------------
/// Sweeping to `hi`, then on
/// ---------------------------------------------------------------------------

let rec crange_from (g: heap) (st: pstate) (ol: U64.t) (p hi: nat)
  : Lemma (requires wreach st.pm p hi)
          (ensures SA.sweep_from g st p ==
                   (let t = crange g st ol p hi in SA.sweep_from (cg t) (cs t) hi))
          (decreases (if p < hi then hi - p else 0))
  = if p = hi then crange_stop g st ol p hi
    else begin
      wreach_next st.pm p hi;
      crange_step g st ol p hi;
      sweep_from_step g st p;
      let (g', st') = SA.step g st p in
      let q = p + span st.pm p in
      step_kinds_from g st p;
      wreach_kinds st'.pm st.pm q hi;
      crange_from g' st' (ostep g st ol p) q hi
    end

let rec crange_trans (g: heap) (st: pstate) (ol: U64.t) (p q hi: nat)
  : Lemma (requires wreach st.pm p q /\ q <= hi)
          (ensures crange g st ol p hi ==
                   (let t = crange g st ol p q in crange (cg t) (cs t) (co t) q hi))
          (decreases (if p < q then q - p else 0))
  = if p = q then crange_stop g st ol p q
    else begin
      wreach_next st.pm p q;
      crange_step g st ol p hi;
      crange_step g st ol p q;
      let (g', st') = SA.step g st p in
      let p' = p + span st.pm p in
      step_kinds_from g st p;
      wreach_kinds st'.pm st.pm p' q;
      crange_trans g' st' (ostep g st ol p) p' q hi
    end

/// ---------------------------------------------------------------------------
/// A unit's sweep and a write outside it
/// ---------------------------------------------------------------------------

/// The word at `x` lies outside `[lo, hi)`.
let out_span (x: nat) (lo hi: nat) : prop = x + 8 <= lo \/ x >= hi

let wr_agree (g: heap) (x: nat) (v: U64.t) (lo hi: nat)
  : Lemma (requires out_span x lo hi) (ensures SO.hagree (B.wr g x v) g lo hi)
  = let aux (y: hp_addr) : Lemma (lo <= U64.v y /\ U64.v y < hi ==> read_word (B.wr g x v) y == read_word g y)
      = B.wr_read g x v y
    in
    FStar.Classical.forall_intro aux

/// **A write outside a unit commutes with its sweep.**
let unit_wr (g: heap) (pm: page_map) (i: nat{i < n_pages}) (fp: U64.t) (x: nat) (v: U64.t)
  : Lemma (requires out_span x (SO.lo_of i) (SO.hi_of pm i))
          (ensures (let t = SO.sweep_unit g pm i fp in
                    let t' = SO.sweep_unit (B.wr g x v) pm i fp in
                    SO.hp t' == B.wr (SO.hp t) x v /\ SO.mp t' == SO.mp t /\ SO.rp t' == SO.rp t))
  = let lo = SO.lo_of i in
    let hi = SO.hi_of pm i in
    let t = SO.sweep_unit g pm i fp in
    let t' = SO.sweep_unit (B.wr g x v) pm i fp in
    wr_agree g x v lo hi;
    SO.unit_local (B.wr g x v) g pm pm i fp;
    SO.unit_frame g pm i fp;
    SO.unit_frame (B.wr g x v) pm i fp;
    let words (a: nat)
      : Lemma (a < heap_size /\ a % 8 == 0 ==>
               read_word (SO.hp t') (U64.uint_to_t a) == read_word (B.wr (SO.hp t) x v) (U64.uint_to_t a))
      = if a < heap_size && a % 8 = 0 then begin
          let y : hp_addr = U64.uint_to_t a in
          B.wr_read (SO.hp t) x v y;
          B.wr_read g x v y
        end
    in
    FStar.Classical.forall_intro words;
    HE.heap_read_word_ext (SO.hp t') (B.wr (SO.hp t) x v);
    let ent (k: nat{k < n_pages}) : Lemma (entry (SO.mp t') k == entry (SO.mp t) k) = () in
    FStar.Classical.forall_intro ent;
    SO.map_eq (SO.mp t') (SO.mp t)

/// **Setting the link of a page outside a unit commutes with its sweep.**
let unit_sn (g: heap) (pm: page_map) (i: nat{i < n_pages}) (fp: U64.t) (q: nat{q < n_pages}) (v: U64.t)
  : Lemma (requires q < i \/ q >= Fr.span_end pm i)
          (ensures (let t = SO.sweep_unit g pm i fp in
                    let t' = SO.sweep_unit g (SS.set_next pm q v) i fp in
                    SO.hp t' == SO.hp t /\ SO.mp t' == SS.set_next (SO.mp t) q v /\ SO.rp t' == SO.rp t))
  = let pm' = SS.set_next pm q v in
    let t = SO.sweep_unit g pm i fp in
    let t' = SO.sweep_unit g pm' i fp in
    assert (entry pm' i == entry pm i);
    assert (Fr.span_end pm' i == Fr.span_end pm i);
    assert (SO.pagree pm' pm i (Fr.span_end pm' i));
    SO.unit_local g g pm' pm i fp;
    SO.unit_frame g pm i fp;
    SO.unit_frame g pm' i fp;
    HE.heap_read_word_ext (SO.hp t') (SO.hp t);
    let ent (k: nat{k < n_pages}) : Lemma (entry (SO.mp t') k == entry (SS.set_next (SO.mp t) q v) k)
      = ()
    in
    FStar.Classical.forall_intro ent;
    SO.map_eq (SO.mp t') (SS.set_next (SO.mp t) q v)

/// ---------------------------------------------------------------------------
/// A step and a write outside its unit
/// ---------------------------------------------------------------------------

/// The step at a pool page or a run is the sweep of its unit.
let step_pool_unit (g: heap) (st: pstate) (p: nat{p < n_pages}) (c: nat{c < n_cls})
  : Lemma (requires not (entry st.pm p).swept /\ (entry st.pm p).kind == Pool c)
          (ensures (let t = SO.sweep_unit g st.pm p 0UL in
                    SA.step g st p == (SO.hp t, SS.push_avail st p (entry (SO.mp t) p))))
  = ()

let step_run_unit (g: heap) (st: pstate) (p: nat{p < n_pages}) (n: pos)
  : Lemma (requires not (entry st.pm p).swept /\ (entry st.pm p).kind == LargeHead n)
          (ensures (let t = SO.sweep_unit g st.pm p (Ce.large_head st) in
                    SA.step g st p == (SO.hp t, SS.run_state st (SO.mp t) (SO.rp t))))
  = ()

let unit_span (pm: page_map) (p: nat{p < n_pages})
  : Lemma (SO.lo_of p == page_base p /\ SO.hi_of pm p == page_base (p + span pm p) /\
           Fr.span_end pm p == p + span pm p)
  = ()

/// The run's layout reads only the run.
let fs_local (g1 g2: heap) (p n: nat)
  : Lemma (requires SO.hagree g1 g2 (page_base p) (page_base (p + n)))
          (ensures run_fs g1 p n == run_fs g2 p n)
  = SO.olds_local g1 g2 (page_base p) (page_base p) (page_base (p + n))

/// **A write outside the unit at `p` commutes with the step there.**
let step_wr (g: heap) (st: pstate) (ol: U64.t) (p: nat{p < n_pages}) (x: nat) (v: U64.t)
  : Lemma (requires out_span x (page_base p) (page_base (p + span st.pm p)))
          (ensures SA.step (B.wr g x v) st p == (B.wr (fst (SA.step g st p)) x v, snd (SA.step g st p)) /\
                   ostep (B.wr g x v) st ol p == ostep g st ol p)
  = unit_span st.pm p;
    if (entry st.pm p).swept then ()
    else match (entry st.pm p).kind with
      | Pool c ->
        step_pool_unit g st p c;
        step_pool_unit (B.wr g x v) st p c;
        unit_wr g st.pm p 0UL x v
      | LargeHead n ->
        step_run_unit g st p n;
        step_run_unit (B.wr g x v) st p n;
        unit_wr g st.pm p (Ce.large_head st) x v;
        wr_agree g x v (page_base p) (page_base (p + n));
        fs_local (B.wr g x v) g p n
      | _ -> ()

/// No list of `st` ends at page `q`.
let tails_not (st: pstate) (q: nat) : prop =
  forall (c: nat{c < n_cls}). c < Seq.length st.atail ==> U64.v (Seq.index st.atail c) <> q + 1

/// The state with page `q`'s link set to `v`.
let with_sn (st: pstate) (q: nat{q < n_pages}) (v: U64.t) : pstate =
  { st with pm = SS.set_next st.pm q v }

/// Setting the link of page `q` commutes with pushing page `p`, when no list
/// ends at `q`.
let push_sn (st: pstate) (p: nat{p < n_pages}) (e: page_info) (q: nat{q < n_pages}) (v: U64.t)
  : Lemma (requires q <> p /\ tails_not st q)
          (ensures SS.push_avail (with_sn st q v) p e == with_sn (SS.push_avail st p e) q v)
  = let a = SS.push_avail (with_sn st q v) p e in
    let b = with_sn (SS.push_avail st p e) q v in
    SS.push_entry st p e;
    SS.push_frame st p e;
    SS.push_entry (with_sn st q v) p e;
    SS.push_frame (with_sn st q v) p e;
    assert (SS.old_tail (with_sn st q v) p e == SS.old_tail st p e);
    let ent (k: nat{k < n_pages}) : Lemma (entry a.pm k == entry b.pm k)
      = ()
    in
    FStar.Classical.forall_intro ent;
    SO.map_eq a.pm b.pm

/// **Setting the link of a page outside the unit at `p` commutes with the
/// step there**, when no list ends at that page.
let step_sn (g: heap) (st: pstate) (ol: U64.t) (p: nat{p < n_pages}) (q: nat{q < n_pages}) (v: U64.t)
  : Lemma (requires (q < p \/ q >= p + span st.pm p) /\ tails_not st q)
          (ensures SA.step g (with_sn st q v) p == (fst (SA.step g st p), with_sn (snd (SA.step g st p)) q v) /\
                   ostep g (with_sn st q v) ol p == ostep g st ol p)
  = unit_span st.pm p;
    assert (entry (with_sn st q v).pm p == entry st.pm p);
    if (entry st.pm p).swept then ()
    else match (entry st.pm p).kind with
      | Pool c ->
        step_pool_unit g st p c;
        step_pool_unit g (with_sn st q v) p c;
        unit_sn g st.pm p 0UL q v;
        let t = SO.sweep_unit g st.pm p 0UL in
        assert (entry (SS.set_next (SO.mp t) q v) p == entry (SO.mp t) p);
        push_sn st p (entry (SO.mp t) p) q v
      | LargeHead n ->
        step_run_unit g st p n;
        step_run_unit g (with_sn st q v) p n;
        unit_sn g st.pm p (Ce.large_head st) q v
      | _ -> ()

/// A step keeps "no list ends at `q`" when `q` lies outside its unit.
let step_tails_not (g: heap) (st: pstate) (p: nat{p < n_pages}) (q: nat)
  : Lemma (requires tails_not st q /\ q <> p)
          (ensures tails_not (snd (SA.step g st p)) q)
  = if (entry st.pm p).swept then ()
    else match (entry st.pm p).kind with
      | Pool c -> SS.push_frame st p (snd (SP.sweep_page g st.pm p))
      | _ -> ()

/// ---------------------------------------------------------------------------
/// A range and a write outside it
/// ---------------------------------------------------------------------------

let page_base_le (a b: nat) : Lemma (requires a <= b) (ensures page_base a <= page_base b)
  = FStar.Math.Lemmas.lemma_mult_le_right page_bytes a b

/// **A write outside the range commutes with sweeping it.**
let rec crange_wr (g: heap) (st: pstate) (ol: U64.t) (p hi: nat) (x: nat) (v: U64.t)
  : Lemma (requires wreach st.pm p hi /\ out_span x (page_base p) (page_base hi))
          (ensures (let t = crange g st ol p hi in
                    crange (B.wr g x v) st ol p hi == (B.wr (cg t) x v, cs t, co t)))
          (decreases (if p < hi then hi - p else 0))
  = if p = hi then begin
      crange_stop g st ol p hi;
      crange_stop (B.wr g x v) st ol p hi
    end else begin
      wreach_next st.pm p hi;
      let q = p + span st.pm p in
      wreach_le st.pm q hi;
      page_base_le p q;
      page_base_le q hi;
      crange_step g st ol p hi;
      crange_step (B.wr g x v) st ol p hi;
      step_wr g st ol p x v;
      let (g', st') = SA.step g st p in
      step_kinds_from g st p;
      wreach_kinds st'.pm st.pm q hi;
      crange_wr g' st' (ostep g st ol p) q hi x v
    end

/// **Setting the link of a page below the range commutes with sweeping
/// it**, when no list ends at that page.
let rec crange_sn (g: heap) (st: pstate) (ol: U64.t) (p hi: nat) (q: nat{q < n_pages}) (v: U64.t)
  : Lemma (requires wreach st.pm p hi /\ q < p /\ tails_not st q)
          (ensures (let t = crange g st ol p hi in
                    crange g (with_sn st q v) ol p hi == (cg t, with_sn (cs t) q v, co t)))
          (decreases (if p < hi then hi - p else 0))
  = if p = hi then begin
      crange_stop g st ol p hi;
      crange_stop g (with_sn st q v) ol p hi
    end else begin
      wreach_next st.pm p hi;
      let p' = p + span st.pm p in
      crange_step g st ol p hi;
      crange_step g (with_sn st q v) ol p hi;
      assert (span (with_sn st q v).pm p == span st.pm p);
      step_sn g st ol p q v;
      let (g', st') = SA.step g st p in
      step_kinds_from g st p;
      wreach_kinds st'.pm st.pm p' hi;
      step_tails_not g st p q;
      crange_sn g' st' (ostep g st ol p) p' hi q v
    end
