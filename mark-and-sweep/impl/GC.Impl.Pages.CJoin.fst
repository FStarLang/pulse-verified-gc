/// ---------------------------------------------------------------------------
/// GC.Impl.Pages.CJoin - joining a chunk's fragments onto the lists
/// ---------------------------------------------------------------------------
///
/// After the chunks are swept, each chunk's record holds its fragments:
/// for each class, the head and tail of its pages with a free slot, and the
/// head of its fragment of list 0 with its open link.  `join_chunk` joins one
/// chunk's fragments onto the allocator's lists, as the prototype's
/// `lists_install`, and computes exactly `SweepSplit.jstep`:
///   - for each class whose fragment is not empty, the old tail's link is set
///     to the fragment's head (or the fragment's head becomes the list's head
///     when the list is empty), and the fragment's tail becomes the list's;
///   - the open link is set to list 0's head, and the fragment's head becomes
///     list 0's head when the fragment is not empty.
/// The classes are joined one at a time (`jst_d`, the join of the classes
/// below `d`); each class's old tail is a page of that class (`jtails`), so
/// the links set for different classes are on different pages.

module GC.Impl.Pages.CJoin

#lang-pulse

open Pulse.Lib.Pervasives
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Inv
open GC.Impl.Heap
open GC.Impl.Pages.Params
open GC.Impl.Pages.State
open GC.Impl.Pages.CState

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module SZ = FStar.SizeT
module Seq = FStar.Seq
module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module Base = GC.Spec.Base
module SH = GC.Spec.Heap
module FLs = GC.Spec.FreeLists
module Ce = GC.Spec.Pages.Cells
module B = GC.Spec.Pages.Blocks
module SO = GC.Spec.Pages.SweepOrder
module SSp = GC.Spec.Pages.SweepSplit

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// A chunk's record: its fragments `f`, its open link `ol`, and the lowest
/// page it left free `mf`.
let frag_rel (q: Seq.seq U64.t) (f: pstate) (ol: U64.t) (mf: nat) : prop =
  Seq.length q == pw /\ sl q 0 n_cls == f.avail /\ sl q n_cls n_cls == f.atail /\
  f.large == FLs.fls_set FLs.fls_empty 0 (Seq.index q o_lh) /\
  Seq.index q o_ol == ol /\ U64.v (Seq.index q o_mf) == mf

/// Each list of `st` ends on a page of its class.
let jtails (st: pstate) (pm: page_map) : prop =
  SSp.lists_ok st /\
  (forall (d: nat{d < n_cls}). SSp.at st.atail d <> 0UL ==>
     U64.v (SSp.at st.atail d) >= 1 /\ U64.v (SSp.at st.atail d) - 1 < n_pages /\
     (entry pm (U64.v (SSp.at st.atail d) - 1)).kind == Pool d)

/// ---------------------------------------------------------------------------
/// The join, a class at a time
/// ---------------------------------------------------------------------------

noextract
let jnx (st f: pstate) (d: nat) (e: page_info) (j: nat) : page_info =
  match e.kind with
  | Pool c -> if c < d then SSp.jnext st f e j else e
  | _ -> e

noextract
let jpm_d (pm: page_map) (st f: pstate) (d: nat) : page_map =
  Seq.init n_pages (fun (j: nat{j < n_pages}) -> jnx st f d (entry pm j) j)

noextract
let jav_d (st f: pstate) (d: nat) : Seq.seq U64.t =
  Seq.init n_cls (fun (c: nat{c < n_cls}) ->
    if c < d then (if SSp.at f.atail c <> 0UL && SSp.at st.atail c = 0UL then SSp.at f.avail c else SSp.at st.avail c)
    else SSp.at st.avail c)

noextract
let jat_d (st f: pstate) (d: nat) : Seq.seq U64.t =
  Seq.init n_cls (fun (c: nat{c < n_cls}) ->
    if c < d then (if SSp.at f.atail c <> 0UL then SSp.at f.atail c else SSp.at st.atail c)
    else SSp.at st.atail c)

/// The state with the classes below `d` joined.
noextract
let jst_d (pm: page_map) (st f: pstate) (d: nat) : pstate =
  { pm = jpm_d pm st f d; avail = jav_d st f d; atail = jat_d st f d; large = st.large }

let jst_start (st: pstate) (f: pstate)
  : Lemma (requires SSp.lists_ok st) (ensures jst_d st.pm st f 0 == st)
  = SO.map_eq (jpm_d st.pm st f 0) st.pm;
    Seq.lemma_eq_intro (jav_d st f 0) st.avail;
    Seq.lemma_eq_intro (jat_d st f 0) st.atail

let jst_end (st: pstate) (f: pstate)
  : Lemma (requires SSp.lists_ok st)
          (ensures jst_d st.pm st f n_cls == { SSp.jst st.pm st f with large = st.large })
  = let ent (j: nat{j < n_pages}) : Lemma (entry (jpm_d st.pm st f n_cls) j == entry (SSp.jpm st.pm st f) j)
      = SSp.entry_jpm st.pm st f j
    in
    FStar.Classical.forall_intro ent;
    SO.map_eq (jpm_d st.pm st f n_cls) (SSp.jpm st.pm st f);
    Seq.lemma_eq_intro (jav_d st f n_cls) (SSp.javail st f);
    Seq.lemma_eq_intro (jat_d st f n_cls) (SSp.jatail st f)

let jst_lens (pm: page_map) (st f: pstate) (d: nat)
  : Lemma (Seq.length (jst_d pm st f d).avail == n_cls /\ Seq.length (jst_d pm st f d).atail == n_cls)
  = ()

/// Class `d` with an empty fragment: nothing changes.
let jst_skip (st f: pstate) (d: nat{d < n_cls})
  : Lemma (requires SSp.at f.atail d == 0UL)
          (ensures jst_d st.pm st f (d + 1) == jst_d st.pm st f d)
  = SO.map_eq (jpm_d st.pm st f (d + 1)) (jpm_d st.pm st f d);
    Seq.lemma_eq_intro (jav_d st f (d + 1)) (jav_d st f d);
    Seq.lemma_eq_intro (jat_d st f (d + 1)) (jat_d st f d)

/// Class `d` joined onto an empty list.
let jst_head (st f: pstate) (d: nat{d < n_cls})
  : Lemma (requires SSp.at f.atail d <> 0UL /\ SSp.at st.atail d == 0UL)
          (ensures jst_d st.pm st f (d + 1) ==
                   set_atail_at (set_avail_at (jst_d st.pm st f d) d (SSp.at f.avail d)) d (SSp.at f.atail d))
  = let x = jst_d st.pm st f d in
    let y = set_atail_at (set_avail_at x d (SSp.at f.avail d)) d (SSp.at f.atail d) in
    SO.map_eq (jpm_d st.pm st f (d + 1)) x.pm;
    Seq.lemma_eq_intro (jav_d st f (d + 1)) y.avail;
    Seq.lemma_eq_intro (jat_d st f (d + 1)) y.atail

#push-options "--z3rlimit 40"
/// Class `d` joined onto a list ending at page `tl - 1`.
let jst_link (st f: pstate) (d: nat{d < n_cls})
  : Lemma (requires SSp.at f.atail d <> 0UL /\ SSp.at st.atail d <> 0UL /\ jtails st st.pm)
          (ensures (let tl = U64.v (SSp.at st.atail d) in
                    tl >= 1 /\ tl - 1 < n_pages /\
                    jst_d st.pm st f (d + 1) ==
                    set_atail_at (set_next_at (jst_d st.pm st f d) (tl - 1) (SSp.at f.avail d)) d (SSp.at f.atail d)))
  = let tl = U64.v (SSp.at st.atail d) in
    let x = jst_d st.pm st f d in
    let y = set_atail_at (set_next_at x (tl - 1) (SSp.at f.avail d)) d (SSp.at f.atail d) in
    let ent (j: nat{j < n_pages}) : Lemma (entry (jpm_d st.pm st f (d + 1)) j == entry y.pm j)
      = if j = tl - 1 then () else ()
    in
    FStar.Classical.forall_intro ent;
    SO.map_eq (jpm_d st.pm st f (d + 1)) y.pm;
    Seq.lemma_eq_intro (jav_d st f (d + 1)) y.avail;
    Seq.lemma_eq_intro (jat_d st f (d + 1)) y.atail
#pop-options

/// ---------------------------------------------------------------------------
/// Reading a chunk's record
/// ---------------------------------------------------------------------------

let rec_at (q: Seq.seq U64.t) (base: nat) (f: pstate) (ol: U64.t) (mf: nat) (k: nat)
  : Lemma (requires base + pw <= Seq.length q /\ frag_rel (Seq.slice q base (base + pw)) f ol mf /\ k < n_cls)
          (ensures Seq.index q (base + k) == SSp.at f.avail k /\
                   Seq.index q (base + n_cls + k) == SSp.at f.atail k /\
                   Seq.index q (base + o_lh) == Ce.large_head f /\
                   Seq.index q (base + o_ol) == ol)
  = w_small ();
    let q' = Seq.slice q base (base + pw) in
    sl_index q' 0 n_cls k;
    sl_index q' n_cls n_cls k;
    FLs.fls_head_set FLs.fls_empty 0 0 (Seq.index q' o_lh)

let lh_same (l: FLs.fl_state)
  : Lemma (requires Seq.length l >= 1) (ensures FLs.fls_set l 0 (FLs.fls_head l 0) == l)
  = Seq.lemma_eq_intro (FLs.fls_set l 0 (FLs.fls_head l 0)) l

ghost fn ps_eq (t: pstate_t) (st1 st2: pstate)
  requires pages_st t st1 ** pure (st1 == st2)
  ensures pages_st t st2
{
  rewrite (pages_st t st1) as (pages_st t st2)
}

let qsz (base k: U64.t) : Pure SZ.t (requires U64.v base + U64.v k < pow2 32) (ensures fun r -> SZ.v r == U64.v base + U64.v k)
  = FStar.Math.Lemmas.pow2_lt_compat 64 32;
    SZ.uint64_to_sizet (U64.add base k)

/// **Join chunk `c`'s fragments** onto the lists: `SweepSplit.jstep`.
fn join_chunk (heap: heap_t) (t: pstate_t) (parts: A.array U64.t) (c: U64.t)
  (#pp: perm) (#q: erased (Seq.seq U64.t)) (#g: erased Base.heap) (#st: erased pstate)
  (#f: erased pstate) (#ol: erased U64.t) (#mf: erased nat)
  requires is_heap heap g ** pages_st t st ** A.pts_to parts #pp q **
           pure (U64.v c < 256 /\ U64.v c * pw + pw <= Seq.length q /\
                 frag_rel (Seq.slice q (U64.v c * pw) (U64.v c * pw + pw)) f ol mf /\
                 jtails st st.pm /\ (reveal ol <> 0UL ==> U64.v (reveal ol) < Base.heap_size /\ U64.v (reveal ol) % 8 == 0))
  ensures exists* g' st'. is_heap heap g' ** pages_st t st' ** A.pts_to parts #pp q **
          pure ((g', st') == SSp.jstep g st f ol)
{
  w_small ();
  cls_above (n_cls - 1);
  cls_bounds (n_cls - 1);
  assert_norm (pow2 20 == 1048576);
  assert_norm (pow2 32 == 4294967296);
  FStar.Math.Lemmas.lemma_mult_le_right pw (U64.v c + 1) 256;
  let base = U64.mul c (pw_u64 ());
  pages_st_lengths t;
  jst_start st f;
  rewrite (pages_st t st) as (pages_st t (jst_d st.pm st f 0));
  let mut d = 0UL;
  while (U64.lt !d n_cls_u64)
    invariant exists* vd.
      R.pts_to d vd ** pages_st t (jst_d st.pm st f (U64.v vd)) ** pure (U64.v vd <= n_cls)
    decreases (n_cls - U64.v !d)
  {
    let vd = !d;
    rec_at q (U64.v base) f ol mf (U64.v vd);
    let ft = parts.(qsz (U64.add base n_cls_u64) vd);
    if (ft = 0UL) {
      jst_skip st f (U64.v vd);
      ps_eq t (jst_d st.pm st f (U64.v vd)) (jst_d st.pm st f (U64.v (U64.add vd 1UL)));
      d := U64.add vd 1UL
    } else {
      let fh = parts.(qsz base vd);
      jst_lens st.pm st f (U64.v vd);
      let tl = read_atail t vd;
      if (tl = 0UL) {
        jst_head st f (U64.v vd);
        write_avail t vd fh;
        write_atail t vd ft;
        ps_eq t (set_atail_at (set_avail_at (jst_d st.pm st f (U64.v vd)) (U64.v vd) fh) (U64.v vd) ft) (jst_d st.pm st f (U64.v (U64.add vd 1UL)));
        d := U64.add vd 1UL
      } else {
        jst_link st f (U64.v vd);
        let pg = U64.sub tl 1UL;
        write_next t pg fh;
        write_atail t vd ft;
        ps_eq t (set_atail_at (set_next_at (jst_d st.pm st f (U64.v vd)) (U64.v pg) fh) (U64.v vd) ft) (jst_d st.pm st f (U64.v (U64.add vd 1UL)));
        d := U64.add vd 1UL
      }
    }
  };
  let vd = !d;
  jst_end st f;
  ps_eq t (jst_d st.pm st f (U64.v vd)) ({ SSp.jst st.pm st f with large = st.large });
  (* list 0 *)
  rec_at q (U64.v base) f ol mf 0;
  let o = parts.(qsz base (o_ol_u64 ()));
  let lh = read_lhead t;
  let flh = parts.(qsz base (o_lh_u64 ()));
  if (o <> 0UL) {
    let oa : Base.hp_addr = o;
    write_word heap oa lh;
    if (flh <> 0UL) {
      write_lhead t flh
    } else {
      lh_same st.large;
      ()
    }
  } else {
    if (flh <> 0UL) {
      write_lhead t flh
    } else {
      lh_same st.large;
      ()
    }
  }
}
