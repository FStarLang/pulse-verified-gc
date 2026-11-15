/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.SweepSplit - sweeping a range from empty lists, then joining
/// ---------------------------------------------------------------------------
///
/// **The list-splitting lemma** (docs/pages-parallel-gc-design.md §2.3,
/// step 3).  Sweeping a range of units from the lists `L` of a state `st`
/// is the same as sweeping it from empty lists, which gives fragments `F`
/// and an open link `ol` (`SweepRange.crange`), and then joining (`jstep`):
///   - for each class, `L ++ F`: the old tail's link set to `F`'s head, which
///     is what `SweepStep.push_avail` does when it appends to a list;
///   - for list 0, `F ++ L`: the open link, the link field of `F`'s last
///     block, set to `L`'s head.  That is `run_head_only`: a run's sweep with
///     list head `fp` and with head 0 differ only in that link, and return the
///     same head unless the run lists nothing (`wr_open`, `lhead_open`).
///
/// It holds when the lists of `st` end below the range (`l_ok`): then the
/// old tails are pages the range does not touch, and the join's writes
/// (`jheap`, `jpm`) commute with the range's sweep, unit by unit
/// (`SweepRange.unit_wr`, and `unit_jpm` here).

module GC.Spec.Pages.SweepSplit

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
open GC.Spec.Pages.SweepRange

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
/// Writes
/// ---------------------------------------------------------------------------

let wr_wr_same (g: heap) (x: nat) (u v: U64.t)
  : Lemma (B.wr (B.wr g x u) x v == B.wr g x v)
  = let aux (a: nat)
      : Lemma (a < heap_size /\ a % 8 == 0 ==>
               read_word (B.wr (B.wr g x u) x v) (U64.uint_to_t a) == read_word (B.wr g x v) (U64.uint_to_t a))
      = if a < heap_size && a % 8 = 0 then begin
          B.wr_read (B.wr g x u) x v (U64.uint_to_t a);
          B.wr_read g x u (U64.uint_to_t a);
          B.wr_read g x v (U64.uint_to_t a)
        end
    in
    FStar.Classical.forall_intro aux;
    HE.heap_read_word_ext (B.wr (B.wr g x u) x v) (B.wr g x v)

let wr_wr_comm (g: heap) (x y: nat) (u v: U64.t)
  : Lemma (requires x <> y) (ensures B.wr (B.wr g x u) y v == B.wr (B.wr g y v) x u)
  = let aux (a: nat)
      : Lemma (a < heap_size /\ a % 8 == 0 ==>
               read_word (B.wr (B.wr g x u) y v) (U64.uint_to_t a) == read_word (B.wr (B.wr g y v) x u) (U64.uint_to_t a))
      = if a < heap_size && a % 8 = 0 then begin
          B.wr_read (B.wr g x u) y v (U64.uint_to_t a);
          B.wr_read g x u (U64.uint_to_t a);
          B.wr_read (B.wr g y v) x u (U64.uint_to_t a);
          B.wr_read g y v (U64.uint_to_t a)
        end
    in
    FStar.Classical.forall_intro aux;
    HE.heap_read_word_ext (B.wr (B.wr g x u) y v) (B.wr (B.wr g y v) x u)

/// ---------------------------------------------------------------------------
/// A run's sweep and its list head
/// ---------------------------------------------------------------------------

/// The open link of a layout lies inside it, past its first word.
#push-options "--fuel 1"
let rec open_in (bs: list blk) (a e: nat)
  : Lemma (requires contig bs a e)
          (ensures open_of bs <> 0UL ==>
                   a + 8 <= U64.v (open_of bs) /\ U64.v (open_of bs) + 8 <= e /\
                   U64.v (open_of bs) % 8 == 0 /\ U64.v (open_of bs) < heap_size)
          (decreases bs)
  = match bs with
    | [] -> ()
    | b :: bs' ->
      open_in bs' (bend b) e;
      contig_le bs' (bend b) e;
      SR.lg_min_ge2 ()

/// The head of a layout's list does not depend on `fp` once it lists a
/// block; then it is not 0.
let rec lhead_open (bs: list blk) (fp: U64.t)
  : Lemma (ensures (open_of bs <> 0UL <==> SR.lhead bs 0UL <> 0UL) /\
                   SR.lhead bs fp == (if open_of bs <> 0UL then SR.lhead bs 0UL else fp))
          (decreases bs)
  = match bs with
    | [] -> ()
    | b :: bs' -> lhead_open bs' fp

/// **`run_head_only`, on the layout**: writing the layout with head `fp` is
/// writing it with head 0 and then setting the open link to `fp`.
let rec wr_open (g0: heap) (bs: list blk) (a e: nat) (fp: U64.t)
  : Lemma (requires contig bs a e)
          (ensures SR.wr_all g0 bs fp ==
                   (if open_of bs <> 0UL then B.wr (SR.wr_all g0 bs 0UL) (U64.v (open_of bs)) fp
                    else SR.wr_all g0 bs 0UL))
          (decreases bs)
  = match bs with
    | [] -> ()
    | b :: bs' ->
      wr_open g0 bs' (bend b) e fp;
      open_in bs' (bend b) e;
      lhead_open bs' fp;
      let o = open_of bs' in
      let w0 = SR.wr_all g0 bs' 0UL in
      let hv = SR.hval g0 b in
      if o <> 0UL then begin
        wr_wr_comm w0 (U64.v o) b.at fp hv;
        if SR.listable b then
          wr_wr_comm (B.wr w0 b.at hv) (U64.v o) (b.at + 8) fp (SR.lhead bs' fp)
      end else begin
        if SR.listable b then
          wr_wr_same (B.wr w0 b.at hv) (b.at + 8) 0UL fp
      end
#pop-options

/// **`run_head_only`, on a run**: the sweep of a run with head `fp` and with
/// head 0 differ only at the open link, and return the same head unless the
/// run lists nothing.
let run_head_only (g: heap) (pm: page_map) (p: nat{p < n_pages}) (n: pos) (fp: U64.t)
  : Lemma (requires (entry pm p).kind == LargeHead n)
          (ensures (let t = SO.sweep_unit g pm p fp in
                    let t0 = SO.sweep_unit g pm p 0UL in
                    let o = open_of (run_fs g p n) in
                    SO.hp t == (if o <> 0UL then B.wr (SO.hp t0) (U64.v o) fp else SO.hp t0) /\
                    SO.mp t == SO.mp t0 /\
                    SO.rp t == (if o <> 0UL then SO.rp t0 else fp) /\
                    (o <> 0UL <==> SO.rp t0 <> 0UL) /\
                    (o <> 0UL ==> page_base p + 8 <= U64.v o /\ U64.v o + 8 <= page_base (p + n) /\
                                  U64.v o % 8 == 0 /\ U64.v o < heap_size)))
  = let s = page_base p in
    let e = page_base (p + n) in
    let fs = run_fs g p n in
    SO.run_bounds p n;
    SO.fin_contig g s e;
    wr_open g fs s (SO.olds_end g s e) fp;
    lhead_open fs fp;
    open_in fs s (SO.olds_end g s e)

/// A run's sweep with a head that is not 0 returns a head that is not 0.
#push-options "--fuel 1"
let rec lhead_nz (bs: list blk) (fp: U64.t)
  : Lemma (requires fp <> 0UL) (ensures SR.lhead bs fp <> 0UL) (decreases bs)
  = match bs with
    | [] -> ()
    | _ :: bs' -> lhead_nz bs' fp
#pop-options

/// ---------------------------------------------------------------------------
/// The join of one range
/// ---------------------------------------------------------------------------

let zcls : Seq.seq U64.t = Seq.create n_cls 0UL

/// `st` with its lists emptied: where a chunk starts.
let empty_lists (st: pstate) : pstate = { st with avail = zcls; atail = zcls; large = FLs.fls_empty }

let lists_ok (st: pstate) : prop =
  Seq.length st.avail == n_cls /\ Seq.length st.atail == n_cls /\ Seq.length st.large == GC.Spec.SizeClass.n_lists

let at (s: Seq.seq U64.t) (c: nat) : U64.t = if c < Seq.length s then Seq.index s c else 0UL

/// Page `j`'s entry `e` after the join of the fragments `f` onto the lists
/// of `st`: the old tail of a class whose fragment is not empty links to the
/// fragment's head.
let jnext_l (st: pstate) (fa ft: Seq.seq U64.t) (e: page_info) (j: nat) : page_info =
  match e.kind with
  | Pool c -> if U64.v (at st.atail c) = j + 1 && at ft c <> 0UL then { e with next = at fa c } else e
  | _ -> e

let jnext (st f: pstate) (e: page_info) (j: nat) : page_info = jnext_l st f.avail f.atail e j

let jpm_l (pm: page_map) (st: pstate) (fa ft: Seq.seq U64.t) : page_map =
  Seq.init n_pages (fun (j: nat{j < n_pages}) -> jnext_l st fa ft (entry pm j) j)

let jpm (pm: page_map) (st f: pstate) : page_map = jpm_l pm st f.avail f.atail

let javail_l (st: pstate) (fa ft: Seq.seq U64.t) : Seq.seq U64.t =
  Seq.init n_cls (fun (c: nat{c < n_cls}) ->
    if at ft c <> 0UL && at st.atail c = 0UL then at fa c else at st.avail c)

let javail (st f: pstate) : Seq.seq U64.t = javail_l st f.avail f.atail

let jatail_l (st: pstate) (ft: Seq.seq U64.t) : Seq.seq U64.t =
  Seq.init n_cls (fun (c: nat{c < n_cls}) -> if at ft c <> 0UL then at ft c else at st.atail c)

let jatail (st f: pstate) : Seq.seq U64.t = jatail_l st f.atail

/// List 0's head after the join: the fragment's, unless it is empty.
let jlh (st f: pstate) : U64.t =
  if Ce.large_head f <> 0UL then Ce.large_head f else Ce.large_head st

/// The open link set to `v`.
let jheap (g: heap) (ol v: U64.t) : GTot heap = if ol <> 0UL then B.wr g (U64.v ol) v else g

/// The state after the join, with the map `pm`.
let jst (pm: page_map) (st f: pstate) : pstate =
  { pm = jpm pm st f; avail = javail st f; atail = jatail st f;
    large = FLs.fls_set st.large 0 (jlh st f) }

/// **The join of one range's fragments** `f`, with open link `ol`, onto the
/// heap `g` and the state `st`.
let jstep (g: heap) (st: pstate) (f: pstate) (ol: U64.t) : GTot (heap & pstate) =
  (jheap g ol (Ce.large_head st), jst st.pm st f)

/// ---------------------------------------------------------------------------
/// What the join needs
/// ---------------------------------------------------------------------------

/// The lists of `st` end below page `lo`, on pages of their class in `pm`.
let l_ok (st: pstate) (lo: nat) (pm: page_map) : prop =
  lists_ok st /\ lo <= n_pages /\
  (forall (c: nat{c < n_cls}). at st.atail c <> 0UL ==>
     U64.v (at st.atail c) >= 1 /\ U64.v (at st.atail c) - 1 < lo /\
     (entry pm (U64.v (at st.atail c) - 1)).kind == Pool c)

/// The fragments `f` of a range from page `lo` swept from empty lists up to
/// page `p`: their tails lie in the range, and the open link, below `p`, is
/// set exactly when list 0's fragment is not empty.
let f_ok (f: pstate) (ol: U64.t) (lo p: nat) : prop =
  lists_ok f /\
  (forall (c: nat{c < n_cls}). at f.atail c <> 0UL ==>
     lo + 1 <= U64.v (at f.atail c) /\ U64.v (at f.atail c) <= p /\ U64.v (at f.atail c) - 1 < n_pages /\
     (entry f.pm (U64.v (at f.atail c) - 1)).kind == Pool c) /\
  (ol = 0UL <==> Ce.large_head f = 0UL) /\
  (ol <> 0UL ==> page_base lo <= U64.v ol /\ U64.v ol + 8 <= page_base p /\
                 U64.v ol % 8 == 0 /\ U64.v ol < heap_size)

let entry_jpm (pm: page_map) (st f: pstate) (j: nat{j < n_pages})
  : Lemma (entry (jpm pm st f) j == jnext st f (entry pm j) j)
  = ()

/// The join changes no entry from page `lo` on.
let jnext_above (st f: pstate) (lo: nat) (pm: page_map) (e: page_info) (j: nat)
  : Lemma (requires l_ok st lo pm /\ j >= lo) (ensures jnext st f e j == e)
  = ()

/// The page sweep reads the map only at its page.
let page_pm (g: heap) (pm1 pm2: page_map) (i: nat{i < n_pages})
  : Lemma (requires entry pm1 i == entry pm2 i) (ensures SP.sweep_page g pm1 i == SP.sweep_page g pm2 i)
  = SO.page_local g g pm1 pm2 i;
    SO.page_frame g pm1 i;
    SO.page_frame g pm2 i;
    HE.heap_read_word_ext (fst (SP.sweep_page g pm1 i)) (fst (SP.sweep_page g pm2 i))

/// **The join's links commute with a unit's sweep** from page `lo` on.
let unit_jpm (g: heap) (pm: page_map) (st f: pstate) (lo: nat) (p: nat{p < n_pages}) (fp: U64.t)
  : Lemma (requires l_ok st lo pm /\ lo <= p)
          (ensures (let t = SO.sweep_unit g pm p fp in
                    let t' = SO.sweep_unit g (jpm pm st f) p fp in
                    SO.hp t' == SO.hp t /\ SO.mp t' == jpm (SO.mp t) st f /\ SO.rp t' == SO.rp t))
  = let pm' = jpm pm st f in
    let t = SO.sweep_unit g pm p fp in
    let t' = SO.sweep_unit g pm' p fp in
    let above (j: nat{j < n_pages}) : Lemma (j >= lo ==> entry pm' j == entry pm j)
      = if j >= lo then (entry_jpm pm st f j; jnext_above st f lo pm (entry pm j) j)
    in
    FStar.Classical.forall_intro above;
    assert (Fr.span_end pm' p == Fr.span_end pm p);
    SO.unit_local g g pm' pm p fp;
    SO.unit_frame g pm p fp;
    SO.unit_frame g pm' p fp;
    HE.heap_read_word_ext (SO.hp t') (SO.hp t);
    let ent (j: nat{j < n_pages}) : Lemma (entry (SO.mp t') j == entry (jpm (SO.mp t) st f) j)
      = entry_jpm (SO.mp t) st f j;
        entry_jpm pm st f j;
        if j >= lo then jnext_above st f lo pm (entry (SO.mp t) j) j
    in
    FStar.Classical.forall_intro ent;
    SO.map_eq (SO.mp t') (jpm (SO.mp t) st f)

/// ---------------------------------------------------------------------------
/// The push and the join
/// ---------------------------------------------------------------------------

let push_plain (st: pstate) (p: nat{p < n_pages}) (e: page_info)
  : Lemma (requires ~(Pool? e.kind /\ e.nfree > 0))
          (ensures SS.push_avail st p e == { st with pm = Seq.upd st.pm p e })
  = ()

let push_pool (st: pstate) (p: nat{p < n_pages}) (e: page_info) (c: nat{c < n_cls})
  : Lemma (requires e.kind == Pool c /\ e.nfree > 0 /\ lists_ok st)
          (ensures (let t = Seq.index st.atail c in
                    let pm1 = Seq.upd st.pm p ({ e with next = 0UL }) in
                    let id = SS.page_id p in
                    SS.push_avail st p e ==
                    { st with pm = (if t = 0UL || U64.v t - 1 >= n_pages || U64.v t - 1 = p then pm1
                                    else SS.set_next pm1 (U64.v t - 1) id);
                              avail = (if t = 0UL then Seq.upd st.avail c id else st.avail);
                              atail = Seq.upd st.atail c id }))
  = ()

let javail_len (st f: pstate) : Lemma (Seq.length (javail st f) == n_cls /\ Seq.length (jatail st f) == n_cls)
  = ()

/// Pushing a page that is not listed: the join is unchanged but for its entry.
let push_join_plain (st f: pstate) (lo: nat) (p: nat{p < n_pages}) (e: page_info)
  : Lemma (requires l_ok st lo f.pm /\ lists_ok f /\ lo <= p /\ ~(Pool? e.kind /\ e.nfree > 0))
          (ensures SS.push_avail (jst f.pm st f) p e ==
                   jst (SS.push_avail f p e).pm st (SS.push_avail f p e))
  = push_plain (jst f.pm st f) p e;
    push_plain f p e;
    let a = Seq.upd (jpm f.pm st f) p e in
    let b = jpm (Seq.upd f.pm p e) st f in
    let ent (j: nat{j < n_pages}) : Lemma (entry a j == entry b j)
      = entry_jpm (Seq.upd f.pm p e) st f j;
        entry_jpm f.pm st f j;
        if j = p then jnext_above st f lo f.pm e p
    in
    FStar.Classical.forall_intro ent;
    SO.map_eq a b;
    let f' = SS.push_avail f p e in
    assert (f'.avail == f.avail /\ f'.atail == f.atail /\ f'.large == f.large);
    assert (javail st f' == javail st f /\ jatail st f' == jatail st f /\ jlh st f' == jlh st f);
    assert (f'.pm == Seq.upd f.pm p e)

#push-options "--z3rlimit 40"
/// Pushing a page of class `c` with a free slot.
let push_join_pool (st f: pstate) (lo: nat) (p: nat{p < n_pages}) (e: page_info) (c: nat{c < n_cls})
  : Lemma (requires l_ok st lo f.pm /\ lists_ok f /\ lo <= p /\ e.kind == Pool c /\ e.nfree > 0 /\
                    (forall (d: nat{d < n_cls}). at f.atail d <> 0UL ==>
                       lo + 1 <= U64.v (at f.atail d) /\ U64.v (at f.atail d) <= p))
          (ensures SS.push_avail (jst f.pm st f) p e ==
                   jst (SS.push_avail f p e).pm st (SS.push_avail f p e))
  = let x = jst f.pm st f in
    let f' = SS.push_avail f p e in
    javail_len st f;
    push_pool x p e c;
    push_pool f p e c;
    let y = SS.push_avail x p e in
    let z = jst f'.pm st f' in
    javail_len st f';
    let id = SS.page_id p in
    let tf = Seq.index f.atail c in
    let ts = at st.atail c in
    assert (Seq.index x.atail c == (if tf <> 0UL then tf else ts));
    (* the lists *)
    let av (d: nat{d < n_cls}) : Lemma (Seq.index y.avail d == Seq.index z.avail d /\
                                       Seq.index y.atail d == Seq.index z.atail d)
      = ()
    in
    FStar.Classical.forall_intro av;
    Seq.lemma_eq_intro y.avail z.avail;
    Seq.lemma_eq_intro y.atail z.atail;
    assert (Ce.large_head f' == Ce.large_head f);
    (* the map *)
    let e0 = { e with next = 0UL } in
    let ent (j: nat{j < n_pages}) : Lemma (entry y.pm j == entry z.pm j)
      = entry_jpm f'.pm st f' j;
        entry_jpm f.pm st f j;
        if j >= lo then begin
          jnext_above st f' lo f.pm (entry f'.pm j) j;
          jnext_above st f lo f.pm (entry f.pm j) j
        end
    in
    FStar.Classical.forall_intro ent;
    SO.map_eq y.pm z.pm
#pop-options

/// **Pushing a page commutes with the join**, when the old lists end below
/// the range and the fragments' inside it.
let push_join (st f: pstate) (lo: nat) (p: nat{p < n_pages}) (e: page_info)
  : Lemma (requires l_ok st lo f.pm /\ lists_ok f /\ lo <= p /\
                    (forall (d: nat{d < n_cls}). at f.atail d <> 0UL ==>
                       lo + 1 <= U64.v (at f.atail d) /\ U64.v (at f.atail d) <= p))
          (ensures SS.push_avail (jst f.pm st f) p e ==
                   jst (SS.push_avail f p e).pm st (SS.push_avail f p e))
  = match e.kind with
    | Pool c -> if e.nfree > 0 then push_join_pool st f lo p e c else push_join_plain st f lo p e
    | _ -> push_join_plain st f lo p e

/// ---------------------------------------------------------------------------
/// The two sweeps of a range, side by side
/// ---------------------------------------------------------------------------

/// The join of a range's fragments `f`, with open link `ol`, swept from empty
/// lists to the heap `g2` and the map `f.pm`, onto the lists of `st`.
let join1 (g2: heap) (f: pstate) (ol: U64.t) (st: pstate) : GTot (heap & pstate) =
  (jheap g2 ol (Ce.large_head st), jst f.pm st f)

/// The sweep from the lists of `st` (`g1`, `st1`) is the join of the sweep
/// from empty lists (`g2`, `st2`, `ol2`).
let rel (g1: heap) (st1: pstate) (g2: heap) (st2: pstate) (ol2: U64.t) (st: pstate) : prop =
  g1 == jheap g2 ol2 (Ce.large_head st) /\ st1 == jst st2.pm st st2

let lh_jst (pm: page_map) (st f: pstate)
  : Lemma (requires lists_ok st) (ensures Ce.large_head (jst pm st f) == jlh st f)
  = FLs.fls_head_set st.large 0 0 (jlh st f)

let fls_set_twice (l: FLs.fl_state) (a b: U64.t)
  : Lemma (FLs.fls_set (FLs.fls_set l 0 a) 0 b == FLs.fls_set l 0 b)
  = if 0 < Seq.length l then Seq.lemma_eq_intro (FLs.fls_set (FLs.fls_set l 0 a) 0 b) (FLs.fls_set l 0 b)

/// A pool page's sweep and a write outside the page.
let page_wr (g: heap) (pm: page_map) (p: nat{p < n_pages}) (c: nat{c < n_cls}) (x: nat) (v: U64.t)
  : Lemma (requires (entry pm p).kind == Pool c /\ out_span x (page_base p) (page_base (p + 1)))
          (ensures SP.sweep_page (B.wr g x v) pm p == (B.wr (fst (SP.sweep_page g pm p)) x v, snd (SP.sweep_page g pm p)))
  = unit_span pm p;
    unit_wr g pm p 0UL x v;
    let t = SO.sweep_unit g pm p 0UL in
    let t' = SO.sweep_unit (B.wr g x v) pm p 0UL in
    assert (Seq.index (SO.mp t') p == Seq.index (SO.mp t) p)

let entry_p (st f: pstate) (lo: nat) (p: nat{p < n_pages})
  : Lemma (requires l_ok st lo f.pm /\ lo <= p) (ensures entry (jst f.pm st f).pm p == entry f.pm p)
  = entry_jpm f.pm st f p; jnext_above st f lo f.pm (entry f.pm p) p

let kinds_below (g: heap) (st2: pstate) (st: pstate) (lo: nat) (p: nat{p < n_pages})
  : Lemma (requires l_ok st lo st2.pm /\ lo <= p) (ensures l_ok st lo (snd (SA.step g st2 p)).pm)
  = let aux (j: nat{j < n_pages}) : Lemma (j < lo ==> (entry (snd (SA.step g st2 p)).pm j).kind == (entry st2.pm j).kind)
      = if j < lo then step_kinds g st2 p j
    in
    FStar.Classical.forall_intro aux

#push-options "--z3rlimit 40"
let split_pool (g1 g2: heap) (st1 st2 st: pstate) (ol2: U64.t) (lo: nat) (p: nat{p < n_pages}) (c: nat{c < n_cls})
  : Lemma (requires rel g1 st1 g2 st2 ol2 st /\ l_ok st lo st2.pm /\ f_ok st2 ol2 lo p /\ lo <= p /\
                    not (entry st2.pm p).swept /\ (entry st2.pm p).kind == Pool c)
          (ensures (let (g1', st1') = SA.step g1 st1 p in
                    let (g2', st2') = SA.step g2 st2 p in
                    rel g1' st1' g2' st2' (ostep g2 st2 ol2 p) st /\
                    f_ok st2' (ostep g2 st2 ol2 p) lo (p + 1)))
  = entry_p st st2 lo p;
    let sp2 = SP.sweep_page g2 st2.pm p in
    page_pm g1 st1.pm st2.pm p;
    if ol2 <> 0UL then begin
      page_base_le p (p + 1);
      page_wr g2 st2.pm p c (U64.v ol2) (Ce.large_head st)
    end;
    let e = snd sp2 in
    push_join st st2 lo p e;
    SS.push_frame st2 p e;
    SS.push_entry st2 p e;
    page_base_le p (p + 1)
#pop-options

let split_other (g1 g2: heap) (st1 st2 st: pstate) (ol2: U64.t) (lo: nat) (p: nat{p < n_pages})
  : Lemma (requires rel g1 st1 g2 st2 ol2 st /\ l_ok st lo st2.pm /\ f_ok st2 ol2 lo p /\ lo <= p /\
                    ((entry st2.pm p).swept \/ ~(Pool? (entry st2.pm p).kind \/ LargeHead? (entry st2.pm p).kind)))
          (ensures (let (g1', st1') = SA.step g1 st1 p in
                    let (g2', st2') = SA.step g2 st2 p in
                    rel g1' st1' g2' st2' (ostep g2 st2 ol2 p) st /\
                    f_ok st2' (ostep g2 st2 ol2 p) lo (p + span st2.pm p)))
  = entry_p st st2 lo p;
    page_base_le p (p + span st2.pm p)

#push-options "--z3rlimit 40"
let split_run_nz (g1 g2: heap) (st1 st2 st: pstate) (ol2: U64.t) (lo: nat) (p: nat{p < n_pages}) (n: pos)
  : Lemma (requires rel g1 st1 g2 st2 ol2 st /\ l_ok st lo st2.pm /\ f_ok st2 ol2 lo p /\ lo <= p /\
                    not (entry st2.pm p).swept /\ (entry st2.pm p).kind == LargeHead n /\
                    Ce.large_head st2 <> 0UL)
          (ensures (let (g1', st1') = SA.step g1 st1 p in
                    let (g2', st2') = SA.step g2 st2 p in
                    rel g1' st1' g2' st2' (ostep g2 st2 ol2 p) st /\
                    f_ok st2' (ostep g2 st2 ol2 p) lo (p + n)))
  = entry_p st st2 lo p;
    lh_jst st2.pm st st2;
    let fp = Ce.large_head st2 in
    step_run_unit g2 st2 p n;
    step_run_unit g1 st1 p n;
    unit_span st2.pm p;
    unit_jpm g1 st2.pm st st2 lo p fp;
    page_base_le p (p + n);
    unit_wr g2 st2.pm p fp (U64.v ol2) (Ce.large_head st);
    let t2 = SO.sweep_unit g2 st2.pm p fp in
    lhead_nz (run_fs g2 p n) fp;
    fls_set_twice st.large (jlh st st2) (SO.rp t2);
    let st2' = SS.run_state st2 (SO.mp t2) (SO.rp t2) in
    assert (st2'.avail == st2.avail /\ st2'.atail == st2.atail);
    FLs.fls_head_set st2.large 0 0 (SO.rp t2)

let split_run_z (g1 g2: heap) (st1 st2 st: pstate) (ol2: U64.t) (lo: nat) (p: nat{p < n_pages}) (n: pos)
  : Lemma (requires rel g1 st1 g2 st2 ol2 st /\ l_ok st lo st2.pm /\ f_ok st2 ol2 lo p /\ lo <= p /\
                    not (entry st2.pm p).swept /\ (entry st2.pm p).kind == LargeHead n /\
                    Ce.large_head st2 == 0UL)
          (ensures (let (g1', st1') = SA.step g1 st1 p in
                    let (g2', st2') = SA.step g2 st2 p in
                    rel g1' st1' g2' st2' (ostep g2 st2 ol2 p) st /\
                    f_ok st2' (ostep g2 st2 ol2 p) lo (p + n)))
  = entry_p st st2 lo p;
    lh_jst st2.pm st st2;
    let fp = Ce.large_head st in
    step_run_unit g2 st2 p n;
    step_run_unit g1 st1 p n;
    unit_span st2.pm p;
    unit_jpm g1 st2.pm st st2 lo p fp;
    page_base_le lo p;
    run_head_only g2 st2.pm p n fp;
    let t2 = SO.sweep_unit g2 st2.pm p 0UL in
    fls_set_twice st.large (jlh st st2) (SO.rp (SO.sweep_unit g2 st2.pm p fp));
    let st2' = SS.run_state st2 (SO.mp t2) (SO.rp t2) in
    assert (st2'.avail == st2.avail /\ st2'.atail == st2.atail);
    FLs.fls_head_set st2.large 0 0 (SO.rp t2)
#pop-options

/// A step keeps the kinds of the pages below it.
let kinds_before (g: heap) (st2: pstate) (p: nat{p < n_pages})
  : Lemma (forall (j: nat{j < n_pages}). j < p ==> (entry (snd (SA.step g st2 p)).pm j).kind == (entry st2.pm j).kind)
  = let aux (j: nat{j < n_pages}) : Lemma (j < p ==> (entry (snd (SA.step g st2 p)).pm j).kind == (entry st2.pm j).kind)
      = if j < p then step_kinds g st2 p j
    in
    FStar.Classical.forall_intro aux

/// One unit of the range, on both sides.
let split_step (g1 g2: heap) (st1 st2 st: pstate) (ol2: U64.t) (lo: nat) (p: nat{p < n_pages})
  : Lemma (requires rel g1 st1 g2 st2 ol2 st /\ l_ok st lo st2.pm /\ f_ok st2 ol2 lo p /\ lo <= p)
          (ensures (let (g1', st1') = SA.step g1 st1 p in
                    let (g2', st2') = SA.step g2 st2 p in
                    span st1.pm p == span st2.pm p /\
                    rel g1' st1' g2' st2' (ostep g2 st2 ol2 p) st /\
                    l_ok st lo st2'.pm /\
                    f_ok st2' (ostep g2 st2 ol2 p) lo (p + span st2.pm p)))
  = entry_p st st2 lo p;
    kinds_below g2 st2 st lo p;
    kinds_before g2 st2 p;
    if (entry st2.pm p).swept then split_other g1 g2 st1 st2 st ol2 lo p
    else match (entry st2.pm p).kind with
      | Pool c -> split_pool g1 g2 st1 st2 st ol2 lo p c
      | LargeHead n ->
        if Ce.large_head st2 <> 0UL then split_run_nz g1 g2 st1 st2 st ol2 lo p n
        else split_run_z g1 g2 st1 st2 st ol2 lo p n
      | _ -> split_other g1 g2 st1 st2 st ol2 lo p

let rec split_from (g1 g2: heap) (st1 st2 st: pstate) (ol1 ol2: U64.t) (lo p hi: nat)
  : Lemma (requires rel g1 st1 g2 st2 ol2 st /\ l_ok st lo st2.pm /\ f_ok st2 ol2 lo p /\ lo <= p /\
                    wreach st2.pm p hi)
          (ensures (let t1 = crange g1 st1 ol1 p hi in
                    let t2 = crange g2 st2 ol2 p hi in
                    rel (cg t1) (cs t1) (cg t2) (cs t2) (co t2) st /\ l_ok st lo (cs t2).pm /\
                    f_ok (cs t2) (co t2) lo hi))
          (decreases (if p < hi then hi - p else 0))
  = if p = hi then begin
      crange_stop g1 st1 ol1 p hi;
      crange_stop g2 st2 ol2 p hi
    end else begin
      wreach_next st2.pm p hi;
      crange_step g1 st1 ol1 p hi;
      crange_step g2 st2 ol2 p hi;
      split_step g1 g2 st1 st2 st ol2 lo p;
      let (g1', st1') = SA.step g1 st1 p in
      let (g2', st2') = SA.step g2 st2 p in
      step_kinds_from g2 st2 p;
      wreach_kinds st2'.pm st2.pm (p + span st2.pm p) hi;
      split_from g1' g2' st1' st2' st (ostep g1 st1 ol1 p) (ostep g2 st2 ol2 p) lo (p + span st2.pm p) hi
    end

/// The state is its own join with empty fragments.
let join_empty (g: heap) (st: pstate)
  : Lemma (requires lists_ok st)
          (ensures rel g st g (empty_lists st) 0UL st /\ f_ok (empty_lists st) 0UL 0 0)
  = let f = empty_lists st in
    let ent (j: nat{j < n_pages}) : Lemma (entry (jpm st.pm st f) j == entry st.pm j)
      = entry_jpm st.pm st f j
    in
    FStar.Classical.forall_intro ent;
    SO.map_eq (jpm st.pm st f) st.pm;
    Seq.lemma_eq_intro (javail st f) st.avail;
    Seq.lemma_eq_intro (jatail st f) st.atail;
    Seq.lemma_eq_intro (FLs.fls_set st.large 0 (jlh st f)) st.large

let f_ok_start (st: pstate) (lo: nat)
  : Lemma (f_ok (empty_lists st) 0UL lo lo)
  = ()

/// A range swept from empty lists keeps its fragments' facts.
let frag_facts (g: heap) (st: pstate) (lo hi: nat)
  : Lemma (requires lists_ok st /\ st.avail == zcls /\ st.atail == zcls /\ st.large == FLs.fls_empty /\
                    lo <= n_pages /\ wreach st.pm lo hi)
          (ensures (let t = crange g st 0UL lo hi in f_ok (cs t) (co t) lo hi))
  = assert (empty_lists st == st);
    join_empty g st;
    f_ok_start st lo;
    split_from g g st st st 0UL 0UL lo lo hi

/// **The list-splitting lemma.**  Sweeping the range `[lo, hi)` from the
/// lists of `st`, which end below `lo`, is sweeping it from empty lists and
/// joining the fragments onto those lists.
let split (g: heap) (st: pstate) (ol: U64.t) (lo hi: nat)
  : Lemma (requires l_ok st lo st.pm /\ wreach st.pm lo hi)
          (ensures (let t1 = crange g st ol lo hi in
                    let t2 = crange g (empty_lists st) 0UL lo hi in
                    (cg t1, cs t1) == join1 (cg t2) (cs t2) (co t2) st /\
                    l_ok st lo (cs t2).pm /\
                    f_ok (cs t2) (co t2) lo hi))
  = join_empty g st;
    f_ok_start st lo;
    split_from g g st (empty_lists st) st ol 0UL lo lo hi

/// ---------------------------------------------------------------------------
/// The open link, as the run sweep keeps it
/// ---------------------------------------------------------------------------

/// The open link is the last listed block's object, as the Pulse run
/// sweep's `pend` holds it.
#push-options "--fuel 2"
let rec open_last (bs: list blk)
  : Lemma (ensures open_of bs == (if Cons? (SR.listed bs) then (L.last (SR.listed bs) <: U64.t) else 0UL))
          (decreases bs)
  = match bs with
    | [] -> ()
    | b :: bs' ->
      open_last bs';
      if SR.listable b && Cons? (SR.listed bs') then
        assert (L.last (SR.listed (b :: bs')) == L.last (SR.listed bs'))
#pop-options

/// A listed block's link lies in the layout.
#push-options "--fuel 1"
let rec listed_in (bs: list blk) (a e: nat) (y: obj_addr)
  : Lemma (requires contig bs a e /\ L.mem y (SR.listed bs))
          (ensures a + 8 <= U64.v y /\ U64.v y + 8 <= e /\ U64.v y % 8 == 0)
          (decreases bs)
  = match bs with
    | c :: r ->
      SR.lg_min_ge2 ();
      contig_le r (bend c) e;
      if SR.listable c && y = SR.obj_at c then () else listed_in r (bend c) e y
#pop-options
