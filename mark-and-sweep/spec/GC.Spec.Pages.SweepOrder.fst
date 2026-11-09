/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.SweepOrder - sweeping two units in either order
/// ---------------------------------------------------------------------------
///
/// A unit is a pool page or a large run.  `sweep_unit` sweeps one: a pool
/// page with `GC.Spec.Pages.SweepPage.sweep_page`, a run with
/// `GC.Spec.Pages.SweepRun.sweep_run`, linking the run's listed blocks in
/// front of the head it is given.
///
/// `sweep_commute` is the plan's `sweep_order_independent`
/// (docs/pages-allocator-proof-plan.md §2.1): sweeping two different units,
/// each with its own list head, in either order gives the same heap and the
/// same page map, and each unit returns the same head.  It rests on two
/// facts about a unit's sweep, both unconditional:
///   - the frame (`unit_frame`): it changes only the words of its span and
///     the entries of its pages;
///   - locality (`unit_local`): what it writes there, and the head it
///     returns, depend only on those words and entries.
/// Two units' spans are disjoint (`apart`), so each sweep leaves the other's
/// input alone.  The order of the lists is the only thing the order of the
/// sweeps decides: it is fixed here by the heads the units are given.

module GC.Spec.Pages.SweepOrder

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Lib.Header
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Shape
open GC.Spec.Pages.Blk
open GC.Spec.Pages.RunList
open GC.Spec.Pages.RunMap

module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot
module PI = GC.Spec.Pages.PoolInit
module IN = GC.Spec.Pages.Init
module SP = GC.Spec.Pages.SweepPage
module SR = GC.Spec.Pages.SweepRun
module Fr = GC.Spec.Pages.Frame
module HE = GC.Gen.HeapExtensional

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Agreement on a stretch
/// ---------------------------------------------------------------------------

/// Two heaps read the same words in `[lo, hi)`.
let hagree (g1 g2: heap) (lo hi: nat) : prop =
  forall (x: hp_addr). lo <= U64.v x /\ U64.v x < hi ==> read_word g1 x == read_word g2 x

/// `g'` is `g` outside `[lo, hi)`.
let hout (g g': heap) (lo hi: nat) : prop =
  forall (x: hp_addr). U64.v x < lo \/ U64.v x >= hi ==> read_word g' x == read_word g x

/// Two maps have the same entries for pages `lo .. hi - 1`.
let pagree (pm1 pm2: page_map) (lo hi: nat) : prop =
  forall (j: nat{j < n_pages}). lo <= j /\ j < hi ==> entry pm1 j == entry pm2 j

/// `pm'` is `pm` outside pages `lo .. hi - 1`.
let pout (pm pm': page_map) (lo hi: nat) : prop =
  forall (j: nat{j < n_pages}). j < lo \/ j >= hi ==> entry pm' j == entry pm j

let hdr_agree (g1 g2: heap) (lo hi: nat) (a: nat)
  : Lemma (requires hagree g1 g2 lo hi /\ lo <= a /\ a < hi)
          (ensures hdr g1 a == hdr g2 a /\ words_at g1 a == words_at g2 a /\
                   color_at g1 a == color_at g2 a)
  = if a < heap_size && a % 8 = 0 then
      assert (read_word g1 (mk_hp_addr a) == read_word g2 (mk_hp_addr a))

/// The same write keeps two heaps in agreement.
let write_agree (h1 h2: heap) (lo hi: nat) (a: hp_addr) (v: U64.t)
  : Lemma (requires hagree h1 h2 lo hi)
          (ensures hagree (write_word h1 a v) (write_word h2 a v) lo hi)
  = let aux (x: hp_addr)
      : Lemma (lo <= U64.v x /\ U64.v x < hi ==>
               read_word (write_word h1 a v) x == read_word (write_word h2 a v) x)
      = if x = a then begin
          read_write_same h1 a v;
          read_write_same h2 a v
        end else begin
          read_write_different h1 a x v;
          read_write_different h2 a x v
        end
    in
    FStar.Classical.forall_intro aux

let page_base_le (a b: nat)
  : Lemma (requires a <= b) (ensures page_base a <= page_base b)
  = FStar.Math.Lemmas.lemma_mult_le_right page_bytes a b

/// ---------------------------------------------------------------------------
/// A pool page
/// ---------------------------------------------------------------------------

let in_page_slot (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat{k < n_slots c})
  : Lemma (page_base i <= slot_base i c k /\ slot_base i c k + 16 <= page_base (i + 1))
  = PI.slot_fits i c k

let live_local (g1 g2: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat)
  : Lemma (requires hagree g1 g2 (page_base i) (page_base (i + 1)) /\ k < n_slots c)
          (ensures SP.live g1 i c k == SP.live g2 i c k)
  = in_page_slot i c k;
    hdr_agree g1 g2 (page_base i) (page_base (i + 1)) (slot_base i c k)

#push-options "--fuel 1"
let rec dead_local (g1 g2: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat)
  : Lemma (requires hagree g1 g2 (page_base i) (page_base (i + 1)) /\ k <= n_slots c)
          (ensures SP.dead_list g1 i c k == SP.dead_list g2 i c k /\
                   SP.hd_upto g1 i c k == SP.hd_upto g2 i c k)
          (decreases k)
  = if k > 0 then begin
      dead_local g1 g2 i c (k - 1);
      live_local g1 g2 i c (k - 1)
    end

let rec any_live_local (g1 g2: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat)
  : Lemma (requires hagree g1 g2 (page_base i) (page_base (i + 1)) /\ k <= n_slots c)
          (ensures SP.any_live g1 i c k == SP.any_live g2 i c k)
          (decreases k)
  = if k > 0 then begin
      any_live_local g1 g2 i c (k - 1);
      live_local g1 g2 i c (k - 1)
    end

/// The swept slots agree on the page.
let rec sw_local (g1 g2: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat{k <= n_slots c})
  : Lemma (requires hagree g1 g2 (page_base i) (page_base (i + 1)))
          (ensures hagree (SP.sw_heap g1 i c k) (SP.sw_heap g2 i c k) (page_base i) (page_base (i + 1)))
          (decreases k)
  = if k > 0 then begin
      let j = k - 1 in
      let lo = page_base i in
      let hi = page_base (i + 1) in
      sw_local g1 g2 i c j;
      live_local g1 g2 i c j;
      dead_local g1 g2 i c j;
      in_page_slot i c j;
      let a = PI.slot_hd i c j in
      let h1 = SP.sw_heap g1 i c j in
      let h2 = SP.sw_heap g2 i c j in
      if SP.live g1 i c j then begin
        assert (read_word g1 a == read_word g2 a);
        write_agree h1 h2 lo hi a (colorHeader (read_word g1 a) White)
      end else begin
        write_agree h1 h2 lo hi a (PI.slot_hdr c);
        write_agree (write_word h1 a (PI.slot_hdr c)) (write_word h2 a (PI.slot_hdr c)) lo hi
          (PI.slot_link i c j) (SP.hd_upto g1 i c j)
      end
    end
#pop-options

/// An address below an aligned bound leaves room for its word.
let below8 (x: hp_addr) (b: nat)
  : Lemma (requires b % 8 == 0 /\ U64.v x < b) (ensures U64.v x + 8 <= b)
  = ()

/// **The page sweep writes only its page.**
let page_frame (g: heap) (pm: page_map) (i: nat{i < n_pages})
  : Lemma (hout g (fst (SP.sweep_page g pm i)) (page_base i) (page_base (i + 1)))
  = page_base_aligned i;
    match (entry pm i).kind with
    | Pool c ->
      if SP.any_live g i c (n_slots c) then begin
        slots_fill_page i c;
        let aux (x: hp_addr)
          : Lemma (U64.v x < page_base i \/ U64.v x >= page_base (i + 1) ==>
                   read_word (SP.sw_heap g i c (n_slots c)) x == read_word g x)
          = if U64.v x < page_base i then (below8 x (page_base i); SP.sw_out g i c (n_slots c) x)
            else if U64.v x >= page_base (i + 1) then SP.sw_out g i c (n_slots c) x
        in
        FStar.Classical.forall_intro aux
      end else begin
        cls_bounds 0;
        let aux (x: hp_addr)
          : Lemma (U64.v x < page_base i \/ U64.v x >= page_base (i + 1) ==>
                   read_word (write_word g (IN.page_addr i) IN.page_hdr) x == read_word g x)
          = if U64.v x < page_base i || U64.v x >= page_base (i + 1) then begin
              page_base_mono i (i + 1);
              if U64.v x < page_base i then below8 x (page_base i);
              read_write_different g (IN.page_addr i) x IN.page_hdr
            end
        in
        FStar.Classical.forall_intro aux
      end
    | _ -> ()

/// **What the page sweep writes depends only on its page and its entry.**
let page_local (g1 g2: heap) (pm1 pm2: page_map) (i: nat{i < n_pages})
  : Lemma (requires hagree g1 g2 (page_base i) (page_base (i + 1)) /\ entry pm1 i == entry pm2 i)
          (ensures snd (SP.sweep_page g1 pm1 i) == snd (SP.sweep_page g2 pm2 i) /\
                   hagree (fst (SP.sweep_page g1 pm1 i)) (fst (SP.sweep_page g2 pm2 i))
                          (page_base i) (page_base (i + 1)))
  = match (entry pm1 i).kind with
    | Pool c ->
      any_live_local g1 g2 i c (n_slots c);
      dead_local g1 g2 i c (n_slots c);
      if SP.any_live g1 i c (n_slots c) then sw_local g1 g2 i c (n_slots c)
      else (cls_bounds 0; write_agree g1 g2 (page_base i) (page_base (i + 1)) (IN.page_addr i) IN.page_hdr)
    | _ -> ()

/// ---------------------------------------------------------------------------
/// A large run
/// ---------------------------------------------------------------------------

/// Where the walk over the run stops.
#push-options "--fuel 1"
let rec olds_end (g: heap) (a e: nat) : Tot nat (decreases (if a < e then e - a else 0)) =
  if a >= e then a
  else begin
    let w = words_at g a in
    if a + w * 8 > e then a else olds_end g (a + w * 8) e
  end

let rec olds_contig (g: heap) (a e: nat)
  : Lemma (ensures contig (olds g a e) a (olds_end g a e) /\ a <= olds_end g a e /\
                   (a <= e ==> olds_end g a e <= e))
          (decreases (if a < e then e - a else 0))
  = if a >= e then ()
    else begin
      let w = words_at g a in
      if a + w * 8 > e then () else olds_contig g (a + w * 8) e
    end

/// The walk over the run reads only the run.
let rec olds_local (g1 g2: heap) (lo a e: nat)
  : Lemma (requires hagree g1 g2 lo e /\ lo <= a)
          (ensures olds g1 a e == olds g2 a e)
          (decreases (if a < e then e - a else 0))
  = if a >= e then ()
    else begin
      hdr_agree g1 g2 lo e a;
      let w = words_at g1 a in
      if a + w * 8 > e then () else olds_local g1 g2 lo (a + w * 8) e
    end
#pop-options

/// The run's layout lies end to end from its start, inside the run, for any
/// heap.
let fin_contig (g: heap) (s e: nat)
  : Lemma (requires s >= z /\ s % 8 == 0 /\ s <= e)
          (ensures contig (fin g s e) s (olds_end g s e) /\ olds_end g s e <= e)
  = olds_contig g s e;
    let e' = olds_end g s e in
    merge_spec (olds g s e) s e';
    split_spec (merge (olds g s e)) s e'

/// The value written at `x` reads the heap only at `x`.
#push-options "--fuel 1"
let rec val_at_local (g1 g2: heap) (lo hi: nat) (bs: list blk) (fp: U64.t) (x: nat)
  : Lemma (requires hagree g1 g2 lo hi /\ lo <= x /\ x < hi)
          (ensures SR.val_at g1 bs fp x == SR.val_at g2 bs fp x)
          (decreases bs)
  = match bs with
    | [] -> ()
    | b :: bs' ->
      if x = b.at then hdr_agree g1 g2 lo hi x
      else val_at_local g1 g2 lo hi bs' fp x
#pop-options

let run_bounds (h: nat) (n: pos)
  : Lemma (page_base h >= z /\ page_base h % 8 == 0 /\ page_base h <= page_base (h + n))
  = page_base_aligned h;
    page_base_le h (h + n)

/// **The run sweep writes only its run and its pages' entries.**
let run_frame (g: heap) (pm: page_map) (h: nat{h < n_pages}) (fp: U64.t)
  : Lemma (requires LargeHead? (entry pm h).kind)
          (ensures (let n = run_len (entry pm h).kind in
                    let (g', pm', _) = SR.sweep_run g pm h fp in
                    hout g g' (page_base h) (page_base (h + n)) /\ pout pm pm' h (h + n)))
  = let n = run_len (entry pm h).kind in
    let s = page_base h in
    let e = page_base (h + n) in
    let fs = fin g s e in
    run_bounds h n;
    fin_contig g s e;
    let aux (x: hp_addr)
      : Lemma (U64.v x < s \/ U64.v x >= e ==> read_word (SR.wr_all g fs fp) x == read_word g x)
      = if U64.v x < s || U64.v x >= e then begin
          SR.va_out g fs s (olds_end g s e) fp (U64.v x);
          SR.wr_all_read g fs fp x
        end
    in
    FStar.Classical.forall_intro aux;
    let ent (j: nat{j < n_pages})
      : Lemma (j < h \/ j >= h + n ==> entry (new_map pm fs h n) j == entry pm j)
      = new_map_entry pm fs h n j
    in
    FStar.Classical.forall_intro ent

/// **What the run sweep writes, and the head it returns, depend only on the
/// run and its pages' entries.**
let run_local (g1 g2: heap) (pm1 pm2: page_map) (h: nat{h < n_pages}) (fp: U64.t)
  : Lemma (requires LargeHead? (entry pm1 h).kind /\ entry pm1 h == entry pm2 h /\
                    hagree g1 g2 (page_base h) (page_base (h + run_len (entry pm1 h).kind)) /\
                    pagree pm1 pm2 h (h + run_len (entry pm1 h).kind))
          (ensures (let n = run_len (entry pm1 h).kind in
                    let (g1', pm1', r1) = SR.sweep_run g1 pm1 h fp in
                    let (g2', pm2', r2) = SR.sweep_run g2 pm2 h fp in
                    hagree g1' g2' (page_base h) (page_base (h + n)) /\
                    pagree pm1' pm2' h (h + n) /\ r1 == r2))
  = let n = run_len (entry pm1 h).kind in
    let s = page_base h in
    let e = page_base (h + n) in
    olds_local g1 g2 s s e;
    let fs = fin g1 s e in
    assert (fin g2 s e == fs);
    let aux (x: hp_addr)
      : Lemma (s <= U64.v x /\ U64.v x < e ==>
               read_word (SR.wr_all g1 fs fp) x == read_word (SR.wr_all g2 fs fp) x)
      = if s <= U64.v x && U64.v x < e then begin
          val_at_local g1 g2 s e fs fp (U64.v x);
          SR.wr_all_read g1 fs fp x;
          SR.wr_all_read g2 fs fp x
        end
    in
    FStar.Classical.forall_intro aux;
    let ent (j: nat{j < n_pages})
      : Lemma (h <= j /\ j < h + n ==> entry (new_map pm1 fs h n) j == entry (new_map pm2 fs h n) j)
      = new_map_entry pm1 fs h n j;
        new_map_entry pm2 fs h n j
    in
    FStar.Classical.forall_intro ent

/// ---------------------------------------------------------------------------
/// Units
/// ---------------------------------------------------------------------------

/// A page that starts a unit: a pool page or the head of a run.
let unit_head (pm: page_map) (i: nat{i < n_pages}) : bool =
  Pool? (entry pm i).kind || LargeHead? (entry pm i).kind

let sweep_unit (g: heap) (pm: page_map) (i: nat{i < n_pages}) (fp: U64.t)
  : GTot (heap & page_map & U64.t)
  = match (entry pm i).kind with
    | Pool c -> let (g', e) = SP.sweep_page g pm i in (g', Seq.upd pm i e, fp)
    | LargeHead n -> SR.sweep_run g pm i fp
    | _ -> (g, pm, fp)

let hp (t: heap & page_map & U64.t) : heap = match t with (g, _, _) -> g
let mp (t: heap & page_map & U64.t) : page_map = match t with (_, pm, _) -> pm
let rp (t: heap & page_map & U64.t) : U64.t = match t with (_, _, r) -> r

/// The words of a unit's span.
let lo_of (i: nat) : nat = page_base i
let hi_of (pm: page_map) (i: nat{i < n_pages}) : nat = page_base (Fr.span_end pm i)

/// **A unit's sweep changes only its span and its pages' entries.**
let unit_frame (g: heap) (pm: page_map) (i: nat{i < n_pages}) (fp: U64.t)
  : Lemma (let t = sweep_unit g pm i fp in
           hout g (hp t) (lo_of i) (hi_of pm i) /\ pout pm (mp t) i (Fr.span_end pm i))
  = match (entry pm i).kind with
    | Pool c -> page_frame g pm i
    | LargeHead n -> run_frame g pm i fp
    | _ -> ()

/// **A unit's sweep depends only on its span and its pages' entries.**
let unit_local (g1 g2: heap) (pm1 pm2: page_map) (i: nat{i < n_pages}) (fp: U64.t)
  : Lemma (requires entry pm1 i == entry pm2 i /\
                    hagree g1 g2 (lo_of i) (hi_of pm1 i) /\
                    pagree pm1 pm2 i (Fr.span_end pm1 i))
          (ensures (let t1 = sweep_unit g1 pm1 i fp in
                    let t2 = sweep_unit g2 pm2 i fp in
                    hagree (hp t1) (hp t2) (lo_of i) (hi_of pm1 i) /\
                    pagree (mp t1) (mp t2) i (Fr.span_end pm1 i) /\
                    rp t1 == rp t2))
  = match (entry pm1 i).kind with
    | Pool c -> page_local g1 g2 pm1 pm2 i
    | LargeHead n -> run_local g1 g2 pm1 pm2 i fp
    | _ -> ()

/// Two units' spans are apart.
let apart (pm: page_map) (i j: nat)
  : Lemma (requires map_ok pm /\ i < n_pages /\ j < n_pages /\ unit_head pm i /\ unit_head pm j /\ i <> j)
          (ensures i < Fr.span_end pm i /\ j < Fr.span_end pm j /\
                   (Fr.span_end pm i <= j \/ Fr.span_end pm j <= i))
  = assert (run_ok pm i);
    assert (run_ok pm j)

/// ---------------------------------------------------------------------------
/// The theorem
/// ---------------------------------------------------------------------------

/// The setting: two different units of a well-formed map.
let two_units (pm: page_map) (i j: nat) : prop =
  map_ok pm /\ i < n_pages /\ j < n_pages /\ unit_head pm i /\ unit_head pm j /\ i <> j

/// Sweeping `j` leaves unit `i`'s input alone.
let other_kept (g: heap) (pm: page_map) (i j: nat) (fpj: U64.t)
  : Lemma (requires two_units pm i j)
          (ensures (let t = sweep_unit g pm j fpj in
                    entry (mp t) i == entry pm i /\
                    Fr.span_end (mp t) i == Fr.span_end pm i /\
                    hagree g (hp t) (lo_of i) (hi_of pm i) /\
                    pagree pm (mp t) i (Fr.span_end pm i)))
  = apart pm i j;
    unit_frame g pm j fpj;
    let se_i = Fr.span_end pm i in
    let se_j = Fr.span_end pm j in
    if se_i <= j then page_base_le se_i j else page_base_le se_j i

/// One order, then the other, word by word.
let word_eq (g: heap) (pm: page_map) (i j: nat) (fpi fpj: U64.t) (x: hp_addr)
  : Lemma (requires two_units pm i j)
          (ensures (let t1 = sweep_unit g pm i fpi in
                    let t2 = sweep_unit g pm j fpj in
                    read_word (hp (sweep_unit (hp t1) (mp t1) j fpj)) x ==
                    read_word (hp (sweep_unit (hp t2) (mp t2) i fpi)) x))
  = let t1 = sweep_unit g pm i fpi in
    let t2 = sweep_unit g pm j fpj in
    other_kept g pm i j fpj;
    other_kept g pm j i fpi;
    unit_local g (hp t2) pm (mp t2) i fpi;
    unit_local g (hp t1) pm (mp t1) j fpj;
    unit_frame (hp t1) (mp t1) j fpj;
    unit_frame (hp t2) (mp t2) i fpi;
    unit_frame g pm i fpi;
    unit_frame g pm j fpj

let entry_eq (g: heap) (pm: page_map) (i j: nat) (fpi fpj: U64.t) (k: nat{k < n_pages})
  : Lemma (requires two_units pm i j)
          (ensures (let t1 = sweep_unit g pm i fpi in
                    let t2 = sweep_unit g pm j fpj in
                    entry (mp (sweep_unit (hp t1) (mp t1) j fpj)) k ==
                    entry (mp (sweep_unit (hp t2) (mp t2) i fpi)) k))
  = let t1 = sweep_unit g pm i fpi in
    let t2 = sweep_unit g pm j fpj in
    other_kept g pm i j fpj;
    other_kept g pm j i fpi;
    unit_local g (hp t2) pm (mp t2) i fpi;
    unit_local g (hp t1) pm (mp t1) j fpj;
    unit_frame (hp t1) (mp t1) j fpj;
    unit_frame (hp t2) (mp t2) i fpi;
    unit_frame g pm i fpi;
    unit_frame g pm j fpj

/// Two maps with the same entries are equal.
let map_eq (pm1 pm2: page_map)
  : Lemma (requires forall (k: nat{k < n_pages}). entry pm1 k == entry pm2 k)
          (ensures pm1 == pm2)
  = let aux (k: nat{k < Seq.length pm1}) : Lemma (Seq.index pm1 k == Seq.index pm2 k)
      = assert (entry pm1 k == entry pm2 k)
    in
    FStar.Classical.forall_intro aux;
    Seq.lemma_eq_intro pm1 pm2

/// **Sweeping two units commutes.**  Sweeping unit `i` with head `fpi` and
/// then unit `j` with head `fpj` gives the same heap and the same page map
/// as sweeping `j` first, and each unit returns the same head either way.
let sweep_commute (g: heap) (pm: page_map) (i j: nat) (fpi fpj: U64.t)
  : Lemma (requires two_units pm i j)
          (ensures (let t1 = sweep_unit g pm i fpi in
                    let t12 = sweep_unit (hp t1) (mp t1) j fpj in
                    let t2 = sweep_unit g pm j fpj in
                    let t21 = sweep_unit (hp t2) (mp t2) i fpi in
                    hp t12 == hp t21 /\ mp t12 == mp t21 /\
                    rp t1 == rp t21 /\ rp t2 == rp t12))
  = let t1 = sweep_unit g pm i fpi in
    let t12 = sweep_unit (hp t1) (mp t1) j fpj in
    let t2 = sweep_unit g pm j fpj in
    let t21 = sweep_unit (hp t2) (mp t2) i fpi in
    let words (a: nat)
      : Lemma (a < heap_size /\ a % 8 == 0 ==>
               read_word (hp t12) (U64.uint_to_t a) == read_word (hp t21) (U64.uint_to_t a))
      = if a < heap_size && a % 8 = 0 then word_eq g pm i j fpi fpj (mk_hp_addr a)
    in
    FStar.Classical.forall_intro words;
    HE.heap_read_word_ext (hp t12) (hp t21);
    FStar.Classical.forall_intro (FStar.Classical.move_requires (entry_eq g pm i j fpi fpj));
    map_eq (mp t12) (mp t21);
    other_kept g pm i j fpj;
    other_kept g pm j i fpi;
    unit_local g (hp t2) pm (mp t2) i fpi;
    unit_local g (hp t1) pm (mp t1) j fpj
