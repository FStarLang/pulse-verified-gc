/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.SweepChunks - the chunked sweep and its join
/// ---------------------------------------------------------------------------
///
/// The parallel sweep of docs/pages-parallel-gc-design.md §2: the pages are
/// cut at bounds `b` into `n` chunks, each starting on a unit (`bounds_ok`);
/// each chunk is swept from empty lists (`chunk`), and then the chunks'
/// fragments are joined onto the lists in ascending chunk order:
/// `sweep_chunks` sweeps the chunks one after another (`chunks`, `frag`) and
/// then applies the joins (`hjoin` to the heap, `pjoin` to the map, `ljoin`
/// to the lists).  Each chunk's sweep owns its own pages, so running the
/// chunks at the same time gives the same result as running them in order.
///
/// **`sweep_chunks_eq`: the chunked sweep is exactly `SweepAll.sweep_all`**,
/// from any state whose lists are empty (as `StartSweep.start_sweep`
/// leaves them).  The proof goes chunk by chunk: the sequential sweep up to
/// chunk `c`'s end is the join of chunk `c`'s fragments onto the sequential
/// sweep up to its start (`SweepSplit.split`), and the joins of the earlier
/// chunks, which write only below chunk `c`, commute with chunk `c`'s sweep
/// (`commute`, from `SweepRange.crange_wr` and `crange_jpm`).

module GC.Spec.Pages.SweepChunks

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Lib.Header
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Inv
open GC.Spec.Pages.SweepRange
open GC.Spec.Pages.SweepSplit

module U64 = FStar.UInt64
module Seq = FStar.Seq
module FLs = GC.Spec.FreeLists
module B = GC.Spec.Pages.Blocks
module SP = GC.Spec.Pages.SweepPage
module SS = GC.Spec.Pages.SweepStep
module SA = GC.Spec.Pages.SweepAll
module SO = GC.Spec.Pages.SweepOrder
module Fr = GC.Spec.Pages.Frame
module Ce = GC.Spec.Pages.Cells
module HE = GC.Gen.HeapExtensional

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// The map `pm` with empty lists: where a chunk's sweep starts.
let zst (pm: page_map) : pstate = { pm = pm; avail = zcls; atail = zcls; large = FLs.fls_empty }

let with_pm (st: pstate) (pm: page_map) : pstate = { st with pm = pm }

/// ---------------------------------------------------------------------------
/// The map below a range
/// ---------------------------------------------------------------------------

/// Two maps agree from page `lo` on.
let agree_from (pm1 pm2: page_map) (lo: nat) : prop =
  forall (j: nat{j < n_pages}). j >= lo ==> entry pm1 j == entry pm2 j

/// Two maps agree below page `lo`.
let agree_below (pm1 pm2: page_map) (lo: nat) : prop =
  forall (j: nat{j < n_pages}). j < lo ==> entry pm1 j == entry pm2 j

/// Every list of `st` ends from page `lo` on.
let tails_ge (st: pstate) (lo: nat) : prop =
  forall (c: nat{c < n_cls}). at st.atail c = 0UL \/ U64.v (at st.atail c) >= lo + 1

let same_lists (s1 s2: pstate) : prop =
  s1.avail == s2.avail /\ s1.atail == s2.atail /\ s1.large == s2.large

#push-options "--z3rlimit 40"
/// A step from page `lo` on reads and writes the map only from `lo` on.
let step_pm (g: heap) (st: pstate) (pm1 pm2: page_map) (ol: U64.t) (lo: nat) (p: nat{p < n_pages})
  : Lemma (requires agree_from pm1 pm2 lo /\ tails_ge st lo /\ lists_ok st /\ lo <= p)
          (ensures (let (g1, s1) = SA.step g (with_pm st pm1) p in
                    let (g2, s2) = SA.step g (with_pm st pm2) p in
                    g1 == g2 /\ same_lists s1 s2 /\ tails_ge s1 lo /\ lists_ok s1 /\
                    agree_from s1.pm s2.pm lo /\ agree_below s1.pm pm1 lo /\ agree_below s2.pm pm2 lo /\
                    span pm1 p == span pm2 p /\
                    ostep g (with_pm st pm1) ol p == ostep g (with_pm st pm2) ol p))
  = let st1 = with_pm st pm1 in
    let st2 = with_pm st pm2 in
    assert (entry pm1 p == entry pm2 p);
    if (entry pm1 p).swept then ()
    else match (entry pm1 p).kind with
      | Pool c ->
        page_pm g pm1 pm2 p;
        let e = snd (SP.sweep_page g pm1 p) in
        SS.push_entry st1 p e;
        SS.push_frame st1 p e;
        SS.push_entry st2 p e;
        SS.push_frame st2 p e
      | LargeHead n ->
        step_run_unit g st1 p n;
        step_run_unit g st2 p n;
        unit_span pm1 p;
        SO.unit_local g g pm1 pm2 p (Ce.large_head st);
        SO.unit_frame g pm1 p (Ce.large_head st);
        SO.unit_frame g pm2 p (Ce.large_head st);
        let t1 = SO.sweep_unit g pm1 p (Ce.large_head st) in
        let t2 = SO.sweep_unit g pm2 p (Ce.large_head st) in
        HE.heap_read_word_ext (SO.hp t1) (SO.hp t2)
      | _ -> ()
#pop-options

/// A range from page `lo` on reads and writes the map only from `lo` on.
let rec crange_pm (g: heap) (st: pstate) (pm1 pm2: page_map) (ol: U64.t) (lo p hi: nat)
  : Lemma (requires agree_from pm1 pm2 lo /\ tails_ge st lo /\ lists_ok st /\ lo <= p)
          (ensures (let t1 = crange g (with_pm st pm1) ol p hi in
                    let t2 = crange g (with_pm st pm2) ol p hi in
                    cg t1 == cg t2 /\ co t1 == co t2 /\ same_lists (cs t1) (cs t2) /\
                    agree_from (cs t1).pm (cs t2).pm lo /\
                    agree_below (cs t1).pm pm1 lo /\ agree_below (cs t2).pm pm2 lo))
          (decreases (if p < hi then hi - p else 0))
  = if p >= hi || p >= n_pages then begin
      crange_stop g (with_pm st pm1) ol p hi;
      crange_stop g (with_pm st pm2) ol p hi
    end else begin
      crange_step g (with_pm st pm1) ol p hi;
      crange_step g (with_pm st pm2) ol p hi;
      step_pm g st pm1 pm2 ol lo p;
      let (g1, s1) = SA.step g (with_pm st pm1) p in
      let (_, s2) = SA.step g (with_pm st pm2) p in
      let ol' = ostep g (with_pm st pm1) ol p in
      assert (with_pm s1 s1.pm == s1);
      assert (with_pm s1 s2.pm == s2);
      crange_pm g1 s1 s1.pm s2.pm ol' lo (p + span pm1 p) hi
    end

/// The lists of `l` end below page `lo`.
let tails_lt (l: pstate) (lo: nat) : prop =
  forall (c: nat{c < n_cls}). at l.atail c <> 0UL ==> U64.v (at l.atail c) >= 1 /\ U64.v (at l.atail c) - 1 < lo

let jnext_lt (l f: pstate) (lo: nat) (e: page_info) (j: nat)
  : Lemma (requires tails_lt l lo /\ j >= lo) (ensures jnext l f e j == e)
  = ()

/// **The join's links commute with a chunk's sweep** when the lists they
/// join onto end below the chunk.
let crange_jpm (g: heap) (pm: page_map) (l f: pstate) (lo hi: nat)
  : Lemma (requires tails_lt l lo)
          (ensures (let t = crange g (zst pm) 0UL lo hi in
                    let t' = crange g (zst (jpm pm l f)) 0UL lo hi in
                    cg t' == cg t /\ co t' == co t /\ cs t' == with_pm (cs t) (jpm (cs t).pm l f)))
  = let pm1 = jpm pm l f in
    let above (j: nat{j < n_pages}) : Lemma (j >= lo ==> entry pm1 j == entry pm j)
      = entry_jpm pm l f j; if j >= lo then jnext_lt l f lo (entry pm j) j
    in
    FStar.Classical.forall_intro above;
    assert (with_pm (zst pm) pm1 == zst pm1);
    assert (with_pm (zst pm) pm == zst pm);
    crange_pm g (zst pm) pm1 pm 0UL lo lo hi;
    let t = crange g (zst pm) 0UL lo hi in
    let t' = crange g (zst pm1) 0UL lo hi in
    let ent (j: nat{j < n_pages}) : Lemma (entry (cs t').pm j == entry (jpm (cs t).pm l f) j)
      = entry_jpm (cs t).pm l f j;
        entry_jpm pm l f j;
        if j >= lo then jnext_lt l f lo (entry (cs t).pm j) j
    in
    FStar.Classical.forall_intro ent;
    SO.map_eq (cs t').pm (jpm (cs t).pm l f)

/// A range keeps the kinds of the pages from `hi` on.
let rec crange_kinds (g: heap) (st: pstate) (ol: U64.t) (p hi: nat)
  : Lemma (requires wreach st.pm p hi)
          (ensures kinds_from (cs (crange g st ol p hi)).pm st.pm hi)
          (decreases (if p < hi then hi - p else 0))
  = if p = hi then crange_stop g st ol p hi
    else begin
      wreach_next st.pm p hi;
      crange_step g st ol p hi;
      let (g', st') = SA.step g st p in
      let q = p + span st.pm p in
      step_kinds_from g st p;
      wreach_kinds st'.pm st.pm q hi;
      wreach_le st.pm q hi;
      crange_kinds g' st' (ostep g st ol p) q hi
    end

/// ---------------------------------------------------------------------------
/// The chunked sweep
/// ---------------------------------------------------------------------------

/// Chunk `c`'s first page.
let bnd (b: Seq.seq U64.t) (c: nat) : nat = if c < Seq.length b then U64.v (Seq.index b c) else n_pages

/// `n` chunks: from page 0 to the end, each starting on a unit.
let bounds_ok (pm: page_map) (b: Seq.seq U64.t) (n: nat) : prop =
  n >= 1 /\ Seq.length b >= n + 1 /\ bnd b 0 == 0 /\ bnd b n == n_pages /\
  (forall (c: nat). c < n ==> bnd b c <= bnd b (c + 1) /\ wreach pm (bnd b c) (bnd b (c + 1)))

/// Chunk `c`, swept from empty lists.
let chunk (g: heap) (pm: page_map) (b: Seq.seq U64.t) (c: nat) : GTot (heap & pstate & U64.t) =
  crange g (zst pm) 0UL (bnd b c) (bnd b (c + 1))

/// Chunks `0 .. c-1`, one after another.
let rec chunks (g: heap) (pm: page_map) (b: Seq.seq U64.t) (c: nat) : GTot (heap & page_map) (decreases c) =
  if c = 0 then (g, pm)
  else begin
    let (g', pm') = chunks g pm b (c - 1) in
    let t = chunk g' pm' b (c - 1) in
    (cg t, (cs t).pm)
  end

/// Chunk `c`'s fragments and open link.
let frag (g: heap) (pm: page_map) (b: Seq.seq U64.t) (c: nat) : GTot (pstate & U64.t) =
  let (g', pm') = chunks g pm b c in
  let t = chunk g' pm' b c in
  (cs t, co t)

/// The lists with fragments `f` joined on.
let jlists (l f: pstate) : pstate =
  { l with avail = javail l f; atail = jatail l f; large = FLs.fls_set l.large 0 (jlh l f) }

/// The lists after the joins of chunks `0 .. c-1`.
let rec ljoin (g0: heap) (pm0: page_map) (b: Seq.seq U64.t) (c: nat) : GTot pstate (decreases c) =
  if c = 0 then zst pm0
  else jlists (ljoin g0 pm0 b (c - 1)) (fst (frag g0 pm0 b (c - 1)))

/// The heap after those joins: each chunk's open link set to the head of
/// the lists before it.
let rec hjoin (g: heap) (g0: heap) (pm0: page_map) (b: Seq.seq U64.t) (c: nat) : GTot heap (decreases c) =
  if c = 0 then g
  else jheap (hjoin g g0 pm0 b (c - 1)) (snd (frag g0 pm0 b (c - 1))) (Ce.large_head (ljoin g0 pm0 b (c - 1)))

/// The map after those joins: each class's old tail linked to the chunk's
/// fragment.
let rec pjoin (pm: page_map) (g0: heap) (pm0: page_map) (b: Seq.seq U64.t) (c: nat) : GTot page_map (decreases c) =
  if c = 0 then pm
  else jpm (pjoin pm g0 pm0 b (c - 1)) (ljoin g0 pm0 b (c - 1)) (fst (frag g0 pm0 b (c - 1)))

/// **The chunked sweep**: every chunk from empty lists, then the joins.
let sweep_chunks (g: heap) (st: pstate) (b: Seq.seq U64.t) (n: nat) : GTot (heap & pstate) =
  let (gc, pmc) = chunks g st.pm b n in
  (hjoin gc g st.pm b n, with_pm (ljoin g st.pm b n) (pjoin pmc g st.pm b n))

/// ---------------------------------------------------------------------------
/// Facts about the chunks
/// ---------------------------------------------------------------------------

#push-options "--fuel 1"
let chunks_unfold (g: heap) (pm: page_map) (b: Seq.seq U64.t) (c: nat)
  : Lemma (chunks g pm b (c + 1) ==
           (let (g', pm') = chunks g pm b c in let t = chunk g' pm' b c in (cg t, (cs t).pm)))
  = ()

let joins_unfold (g g0: heap) (pm pm0: page_map) (b: Seq.seq U64.t) (c: nat)
  : Lemma (ljoin g0 pm0 b (c + 1) == jlists (ljoin g0 pm0 b c) (fst (frag g0 pm0 b c)) /\
           hjoin g g0 pm0 b (c + 1) ==
             jheap (hjoin g g0 pm0 b c) (snd (frag g0 pm0 b c)) (Ce.large_head (ljoin g0 pm0 b c)) /\
           pjoin pm g0 pm0 b (c + 1) == jpm (pjoin pm g0 pm0 b c) (ljoin g0 pm0 b c) (fst (frag g0 pm0 b c)))
  = ()

let joins_zero (g g0: heap) (pm pm0: page_map) (b: Seq.seq U64.t)
  : Lemma (ljoin g0 pm0 b 0 == zst pm0 /\ hjoin g g0 pm0 b 0 == g /\ pjoin pm g0 pm0 b 0 == pm)
  = ()

let chunks_zero (g: heap) (pm: page_map) (b: Seq.seq U64.t) : Lemma (chunks g pm b 0 == (g, pm)) = ()
#pop-options

let bounds_at (pm: page_map) (b: Seq.seq U64.t) (n: nat) (c: nat)
  : Lemma (requires bounds_ok pm b n /\ c < n)
          (ensures bnd b c <= bnd b (c + 1) /\ wreach pm (bnd b c) (bnd b (c + 1)))
  = ()

let bnd_mono (pm: page_map) (b: Seq.seq U64.t) (n: nat) (c d: nat)
  : Lemma (requires bounds_ok pm b n /\ c <= d /\ d <= n) (ensures bnd b c <= bnd b d)
  = let rec aux (k: nat) : Lemma (requires c <= k /\ k <= d) (ensures bnd b c <= bnd b k) (decreases k)
      = if k > c then aux (k - 1)
    in
    aux d

/// The walk lands on every bound.
#push-options "--fuel 1"
let rec wreach_trans (pm: page_map) (p q r: nat)
  : Lemma (requires wreach pm p q /\ wreach pm q r) (ensures wreach pm p r)
          (decreases (if p < q then q - p else 0))
  = if p = q then ()
    else begin
      wreach_next pm p q;
      wreach_le pm q r;
      wreach_trans pm (p + span pm p) q r
    end
#pop-options

#push-options "--fuel 1"
let rec wreach_prefix (pm: page_map) (b: Seq.seq U64.t) (n: nat) (c: nat)
  : Lemma (requires bounds_ok pm b n /\ c <= n) (ensures wreach pm 0 (bnd b c)) (decreases c)
  = if c = 0 then ()
    else begin
      wreach_prefix pm b n (c - 1);
      bounds_at pm b n (c - 1);
      wreach_trans pm 0 (bnd b (c - 1)) (bnd b c)
    end
#pop-options

/// The chunks before `c` keep the kinds of the pages from chunk `c` on.
let rec chunks_kinds (g: heap) (pm: page_map) (b: Seq.seq U64.t) (n: nat) (c: nat)
  : Lemma (requires bounds_ok pm b n /\ c <= n)
          (ensures kinds_from (snd (chunks g pm b c)) pm (bnd b c))
          (decreases c)
  = if c = 0 then chunks_zero g pm b
    else begin
      chunks_kinds g pm b n (c - 1);
      bounds_at pm b n (c - 1);
      chunks_unfold g pm b (c - 1);
      let (g', pm') = chunks g pm b (c - 1) in
      wreach_kinds pm' pm (bnd b (c - 1)) (bnd b c);
      crange_kinds g' (zst pm') 0UL (bnd b (c - 1)) (bnd b c)
    end

/// Chunk `c`'s fragments lie in it.
let frag_ok (g: heap) (pm: page_map) (b: Seq.seq U64.t) (n: nat) (c: nat)
  : Lemma (requires bounds_ok pm b n /\ c < n)
          (ensures f_ok (fst (frag g pm b c)) (snd (frag g pm b c)) (bnd b c) (bnd b (c + 1)))
  = chunks_kinds g pm b n c;
    bounds_at pm b n c;
    let (g', pm') = chunks g pm b c in
    wreach_kinds pm' pm (bnd b c) (bnd b (c + 1));
    bnd_mono pm b n c n;
    frag_facts g' (zst pm') (bnd b c) (bnd b (c + 1))

/// The lists after the joins of chunks `0 .. c-1` end below chunk `c`.
let rec ljoin_tails (g: heap) (pm: page_map) (b: Seq.seq U64.t) (n: nat) (c: nat)
  : Lemma (requires bounds_ok pm b n /\ c <= n)
          (ensures tails_lt (ljoin g pm b c) (bnd b c) /\ lists_ok (ljoin g pm b c))
          (decreases c)
  = joins_zero g g pm pm b;
    if c > 0 then begin
      ljoin_tails g pm b n (c - 1);
      frag_ok g pm b n (c - 1);
      bounds_at pm b n (c - 1);
      joins_unfold g g pm pm b (c - 1);
      javail_len (ljoin g pm b (c - 1)) (fst (frag g pm b (c - 1)))
    end

/// ---------------------------------------------------------------------------
/// The joins commute with a later chunk
/// ---------------------------------------------------------------------------

let rec commute (g0: heap) (pm0: page_map) (b: Seq.seq U64.t) (n: nat) (c: nat)
                (xg: heap) (xpm: page_map) (lo hi: nat)
  : Lemma (requires bounds_ok pm0 b n /\ c <= n /\ bnd b c <= lo /\ wreach xpm lo hi)
          (ensures (let t = crange xg (zst xpm) 0UL lo hi in
                    let t' = crange (hjoin xg g0 pm0 b c) (zst (pjoin xpm g0 pm0 b c)) 0UL lo hi in
                    cg t' == hjoin (cg t) g0 pm0 b c /\ co t' == co t /\
                    cs t' == with_pm (cs t) (pjoin (cs t).pm g0 pm0 b c)))
          (decreases c)
  = let t = crange xg (zst xpm) 0UL lo hi in
    if c = 0 then begin
      joins_zero xg g0 xpm pm0 b;
      joins_zero (cg t) g0 (cs t).pm pm0 b;
      assert (with_pm (cs t) (cs t).pm == cs t)
    end else begin
      let d = c - 1 in
      joins_unfold xg g0 xpm pm0 b d;
      joins_unfold (cg t) g0 (cs t).pm pm0 b d;
      bnd_mono pm0 b n d c;
      commute g0 pm0 b n d xg xpm lo hi;
      let h = hjoin xg g0 pm0 b d in
      let p = pjoin xpm g0 pm0 b d in
      let l = ljoin g0 pm0 b d in
      let (f, ol) = frag g0 pm0 b d in
      frag_ok g0 pm0 b n d;
      ljoin_tails g0 pm0 b n d;
      (* the map: jpm moves out *)
      let kp (j: nat{j < n_pages}) : Lemma ((entry (jpm p l f) j).kind == (entry p j).kind)
        = entry_jpm p l f j
      in
      FStar.Classical.forall_intro kp;
      let rec kq (k: nat) : Lemma (requires k <= d) (ensures kinds_from (pjoin xpm g0 pm0 b k) xpm lo) (decreases k)
        = joins_zero xg g0 xpm pm0 b;
          if k > 0 then begin
            kq (k - 1);
            joins_unfold xg g0 xpm pm0 b (k - 1);
            let aux (j: nat{j < n_pages})
              : Lemma ((entry (pjoin xpm g0 pm0 b k) j).kind == (entry (pjoin xpm g0 pm0 b (k - 1)) j).kind)
              = entry_jpm (pjoin xpm g0 pm0 b (k - 1)) (ljoin g0 pm0 b (k - 1)) (fst (frag g0 pm0 b (k - 1))) j
            in
            FStar.Classical.forall_intro aux
          end
      in
      kq d;
      wreach_kinds p xpm lo hi;
      crange_jpm (jheap h ol (Ce.large_head l)) p l f lo hi;
      (* the heap: the open link moves out *)
      if ol <> 0UL then begin
        page_base_le (bnd b c) lo;
        crange_wr h (zst p) 0UL lo hi (U64.v ol) (Ce.large_head l)
      end
    end

/// ---------------------------------------------------------------------------
/// The theorem
/// ---------------------------------------------------------------------------

/// The joins read only the lists of the state they join onto.
let jst_cong (pm: page_map) (x y f f': pstate)
  : Lemma (requires same_lists x y /\ same_lists f f')
          (ensures jst pm x f == jst pm y f')
  = let ent (j: nat{j < n_pages}) : Lemma (entry (jpm pm x f) j == entry (jpm pm y f') j)
      = entry_jpm pm x f j; entry_jpm pm y f' j
    in
    FStar.Classical.forall_intro ent;
    SO.map_eq (jpm pm x f) (jpm pm y f');
    Seq.lemma_eq_intro (javail x f) (javail y f');
    Seq.lemma_eq_intro (jatail x f) (jatail y f')

/// The sequential sweep up to chunk `c`'s start is the chunks before it,
/// joined.
let claim (g: heap) (st: pstate) (b: Seq.seq U64.t) (c: nat) : prop =
  let q = crange g st 0UL 0 (bnd b c) in
  let (gc, pmc) = chunks g st.pm b c in
  cg q == hjoin gc g st.pm b c /\ cs q == with_pm (ljoin g st.pm b c) (pjoin pmc g st.pm b c)

let empty_st (st: pstate) : prop =
  st.avail == zcls /\ st.atail == zcls /\ st.large == FLs.fls_empty

let claim_zero (g: heap) (st: pstate) (b: Seq.seq U64.t) (n: nat)
  : Lemma (requires empty_st st /\ bounds_ok st.pm b n) (ensures claim g st b 0)
  = crange_stop g st 0UL 0 (bnd b 0);
    chunks_zero g st.pm b;
    joins_zero g g st.pm st.pm b

#push-options "--z3rlimit 40"
let claim_step (g: heap) (st: pstate) (b: Seq.seq U64.t) (n: nat) (c: nat)
  : Lemma (requires empty_st st /\ bounds_ok st.pm b n /\ c < n /\ claim g st b c)
          (ensures claim g st b (c + 1))
  = let lo = bnd b c in
    let hi = bnd b (c + 1) in
    let q = crange g st 0UL 0 lo in
    wreach_prefix st.pm b n c;
    bounds_at st.pm b n c;
    crange_trans g st 0UL 0 lo hi;
    (* the sweep so far, from empty lists, has its lists below `lo` *)
    bnd_mono st.pm b n c n;
    assert (empty_lists st == st);
    frag_facts g st 0 lo;
    crange_kinds g st 0UL 0 lo;
    wreach_kinds (cs q).pm st.pm lo hi;
    split (cg q) (cs q) (co q) lo hi;
    let t2 = crange (cg q) (empty_lists (cs q)) 0UL lo hi in
    assert (empty_lists (cs q) == zst (cs q).pm);
    (* chunk c, on the chunks before it, unjoined *)
    let (gc, pmc) = chunks g st.pm b c in
    chunks_kinds g st.pm b n c;
    wreach_kinds pmc st.pm lo hi;
    commute g st.pm b n c gc pmc lo hi;
    let t = chunk gc pmc b c in
    chunks_unfold g st.pm b c;
    joins_unfold (cg t) g (cs t).pm st.pm b c;
    let l = ljoin g st.pm b c in
    let f = fst (frag g st.pm b c) in
    jst_cong (pjoin (cs t).pm g st.pm b c) (cs q) l (cs t2) f
#pop-options

let rec claim_upto (g: heap) (st: pstate) (b: Seq.seq U64.t) (n: nat) (c: nat)
  : Lemma (requires empty_st st /\ bounds_ok st.pm b n /\ c <= n) (ensures claim g st b c) (decreases c)
  = if c = 0 then claim_zero g st b n
    else begin
      claim_upto g st b n (c - 1);
      claim_step g st b n (c - 1)
    end

/// **The chunked sweep is the sequential sweep.**  From a state with empty
/// lists, sweeping every chunk from empty lists and then joining the
/// fragments in ascending chunk order gives exactly `SweepAll.sweep_all`.
let sweep_chunks_eq (g: heap) (st: pstate) (b: Seq.seq U64.t) (n: nat)
  : Lemma (requires empty_st st /\ bounds_ok st.pm b n)
          (ensures sweep_chunks g st b n == SA.sweep_all g st)
  = claim_upto g st b n n;
    wreach_prefix st.pm b n n;
    crange_from g st 0UL 0 n_pages;
    sweep_from_end (cg (crange g st 0UL 0 n_pages)) (cs (crange g st 0UL 0 n_pages)) n_pages

/// ---------------------------------------------------------------------------
/// The map stays well formed
/// ---------------------------------------------------------------------------

let set_next_map_ok (pm: page_map) (q: nat{q < n_pages}) (v: U64.t)
  : Lemma (requires map_ok pm) (ensures map_ok (SS.set_next pm q v))
  = let pm' = SS.set_next pm q v in
    let aux (j: nat{j < n_pages}) : Lemma (run_ok pm' j /\ cont_ok pm' j /\ free_ok pm' j)
      = assert (run_ok pm j /\ cont_ok pm j /\ free_ok pm j);
        match (entry pm j).kind with
        | LargeCont ->
          eliminate exists (u: nat{u < n_pages}). u < j /\ in_run pm u j
          with assert (in_run pm' u j)
        | _ -> ()
    in
    FStar.Classical.forall_intro aux

/// **A step keeps the map well formed.**
let step_map_ok (g: heap) (st: pstate) (p: nat{p < n_pages})
  : Lemma (requires map_ok st.pm) (ensures map_ok (snd (SA.step g st p)).pm)
  = if (entry st.pm p).swept then ()
    else match (entry st.pm p).kind with
      | Pool c ->
        let e = snd (SP.sweep_page g st.pm p) in
        let st1 = SS.push0 st p e in
        let e0 = if e.nfree > 0 && Seq.length st.avail = n_cls && Seq.length st.atail = n_cls then { e with next = 0UL } else e in
        assert (st1.pm == Seq.upd st.pm p e0);
        GC.Spec.Pages.SweepStep.map_ok_pool st.pm p e0;
        (match SS.old_tail st p e with
         | None -> ()
         | Some q -> set_next_map_ok st1.pm q (SS.page_id p))
      | LargeHead n ->
        GC.Spec.Pages.RunMap.new_map_ok st.pm (run_fs g p n) p n
      | _ -> ()

let rec crange_map_ok (g: heap) (st: pstate) (ol: U64.t) (p hi: nat)
  : Lemma (requires map_ok st.pm) (ensures map_ok (cs (crange g st ol p hi)).pm)
          (decreases (if p < hi then hi - p else 0))
  = if p >= hi || p >= n_pages then crange_stop g st ol p hi
    else begin
      crange_step g st ol p hi;
      step_map_ok g st p;
      let (g', st') = SA.step g st p in
      crange_map_ok g' st' (ostep g st ol p) (p + span st.pm p) hi
    end

/// **The chunks keep the map well formed.**
let rec chunks_map_ok (g: heap) (pm: page_map) (b: Seq.seq U64.t) (c: nat)
  : Lemma (requires map_ok pm) (ensures map_ok (snd (chunks g pm b c))) (decreases c)
  = chunks_zero g pm b;
    if c > 0 then begin
      chunks_map_ok g pm b (c - 1);
      chunks_unfold g pm b (c - 1);
      let (g', pm') = chunks g pm b (c - 1) in
      crange_map_ok g' (zst pm') 0UL (bnd b (c - 1)) (bnd b c)
    end
