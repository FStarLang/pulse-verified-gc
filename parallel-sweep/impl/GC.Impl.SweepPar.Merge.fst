(*
   Pulse GC - Parallel sweep: the merge

   GC.Impl.SweepPar.merge is defined as `merge` here; its signature is the
   interface's, word for word (docs/parallel-sweep-phase1.md, §8).

   The model's link_all, on the whole heap: left to right over the
   segments' records, carry the pending run through all-free segments; at
   a segment with a survivor, flush the carried run joined with its leading
   run (GC.Impl.Coalesce.flush_blue_impl, as the sequential pass), patch
   its first linked block to the head that flush returns, and continue
   from its local head and trailing run.  Flush the carry at the end.

   flush_blue_impl needs each run inside the heap.  That is proved from the
   segments' own outputs (GC.Spec.SweepPar.SegLoop.seg_geom): a leading run
   starts at its segment's first object, and every run ends by its
   segment's end.  The patch keeps the model's own guard, at run time.
*)

module GC.Impl.SweepPar.Merge

#lang-pulse

open Pulse.Lib.Pervasives
open GC.Impl.Heap
open GC.Impl.SweepSegment
module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module Seq = FStar.Seq
module Base = GC.Spec.Base
module SpecHeap = GC.Spec.Heap
module SP = GC.Spec.SweepPar
module SL = GC.Spec.SweepPar.SegLoop
module SC = GC.Spec.Coalesce
module CC = GC.Spec.Coalesce.Correct
module CL = GC.Impl.Coalesce.Lemmas
module Coalesce = GC.Impl.Coalesce

/// ---------------------------------------------------------------------------
/// Records (as in GC.Impl.SweepPar)
/// ---------------------------------------------------------------------------

/// The first m records of `rs` are the model's segment outputs `ms`, in
/// order.  The same definition as GC.Impl.SweepPar.results_match.
let results_match (rs: Seq.seq seg_result) (m: nat) (ms: list SP.seg) : prop =
  m <= Seq.length rs /\
  List.Tot.length ms == m /\
  (forall (i: nat). i < m ==> result_matches (Seq.index rs i) (List.Tot.index ms i).SP.out)

/// ---------------------------------------------------------------------------
/// The segments, in order
/// ---------------------------------------------------------------------------

/// The segments from `b` on: each starts where the last ended, the last
/// ends at heap_size, and each one's runs lie as SL.out_geom says.
let rec chain (b: nat) (rs: list SP.seg) : Tot prop (decreases rs) =
  match rs with
  | [] -> b == heap_size
  | r :: rest -> r.SP.lo == b /\ SL.out_geom r.SP.lo r.SP.hi r.SP.out /\ chain r.SP.hi rest

#push-options "--fuel 2 --ifuel 1"
let rec bounds_chain (g: heap_state) (prev: nat) (bs: list nat)
  : Lemma (requires SP.bounds_from g prev bs /\ prev % 8 == 0 /\ prev < heap_size /\
                    CC.walk_visits g Base.zero_addr (Base.mk_hp_addr prev))
          (ensures chain prev (SP.sweep_all g (SP.segments (prev :: bs))))
          (decreases bs)
  = match bs with
    | b :: rest ->
      SP.bounds_next g prev b rest;
      SP.walk_step g prev b rest;
      SL.seg_geom g (Base.mk_hp_addr prev) b;
      if b < heap_size then bounds_chain g b rest
#pop-options

/// The list from index i on.
let rec drop (l: list SP.seg) (i: nat) : Tot (list SP.seg) (decreases l) =
  if i = 0 then l else match l with [] -> [] | _ :: t -> drop t (i - 1)

#push-options "--fuel 2 --ifuel 1"
let rec drop_cons (l: list SP.seg) (i: nat)
  : Lemma (requires i < List.Tot.length l)
          (ensures drop l i == List.Tot.index l i :: drop l (i + 1))
          (decreases l)
  = if i = 0 then () else drop_cons (List.Tot.tl l) (i - 1)

let rec drop_all (l: list SP.seg) (i: nat)
  : Lemma (requires i >= List.Tot.length l) (ensures drop l i == []) (decreases l)
  = match l with [] -> () | _ :: t -> if i = 0 then () else drop_all t (i - 1)
#pop-options

/// Where the remaining segments start: the first one's lo, or heap_size.
let bound_of (rest: list SP.seg) : nat =
  match rest with r :: _ -> r.SP.lo | [] -> heap_size

/// ---------------------------------------------------------------------------
/// The invariant
/// ---------------------------------------------------------------------------

/// The carried run, when there is one, ends by `b`.
let carry_ok (b: nat) (c: SP.run) : prop =
  c.SP.rw > 0 ==>
    U64.v c.SP.fb >= 8 /\ U64.v c.SP.fb < heap_size /\ U64.v c.SP.fb % 8 == 0 /\
    U64.v c.SP.fb - 8 + c.SP.rw * 8 <= b

/// flush_blue_impl's precondition on a run of rw words.
let run_okn (fb: U64.t) (rw: nat) : prop =
  rw > 0 ==>
    rw < pow2 54 /\ U64.v fb >= 8 /\ U64.v fb < heap_size /\ U64.v fb % 8 == 0 /\
    U64.v fb - 8 + rw * 8 <= heap_size

let run_ok (fb rw: U64.t) : prop = run_okn fb (U64.v rw)

/// Linking the rest from this state gives sweep_par, and every run the rest
/// will flush lies in the heap.
[@@"opaque_to_smt"]
let merge_inv (g: heap_state) (bs: list nat) (rest: list SP.seg) (h: heap_state)
    (cfb crw fp: U64.t) : prop =
  SP.link_all h (SL.mk_run cfb crw) fp rest == SP.sweep_par bs g /\
  chain (bound_of rest) rest /\
  carry_ok (bound_of rest) (SL.mk_run cfb crw)

let pow2_57 () : Lemma (pow2 57 == 8 * pow2 54 /\ pow2 54 < pow2 64)
  = assert_norm (pow2 57 == 8 * pow2 54 /\ pow2 54 < pow2 64)

#push-options "--fuel 1 --ifuel 1"
let merge_entry (g: heap_state) (bs: list nat)
  : Lemma (requires SP.valid_bounds g bs)
          (ensures (let all = SP.sweep_all g (SP.segments bs) in
                    merge_inv g bs all (SP.splice_all g all) 0UL 0UL 0UL))
  = reveal_opaque (`%merge_inv) merge_inv;
    match bs with
    | b0 :: rest ->
      assert (Base.mk_hp_addr b0 == Base.zero_addr);
      bounds_chain g b0 rest
#pop-options

/// The next segment's record: whether the join with its leading run fits.
#push-options "--fuel 1 --ifuel 1"
let merge_head (g: heap_state) (bs: list nat) (r: SP.seg) (rest: list SP.seg)
    (h: heap_state) (cfb crw fp: U64.t) (res: seg_result)
  : Lemma (requires merge_inv g bs (r :: rest) h cfb crw fp /\ result_matches res r.SP.out)
          (ensures (let s = U64.v crw + U64.v res.lead_rw in
                    s < pow2 54 /\
                    run_okn (if U64.v crw = 0 then res.lead_fb else cfb) s))
  = reveal_opaque (`%merge_inv) merge_inv;
    pow2_57 ()
#pop-options

/// An all-free segment: the carry grows by its leading run.
#push-options "--fuel 2 --ifuel 1"
let merge_free (g: heap_state) (bs: list nat) (r: SP.seg) (rest: list SP.seg)
    (h: heap_state) (cfb crw fp: U64.t) (res: seg_result) (nfb nrw: U64.t)
  : Lemma (requires merge_inv g bs (r :: rest) h cfb crw fp /\ result_matches res r.SP.out /\
                    res.all_free == true /\
                    nfb == (if U64.v crw = 0 then res.lead_fb else cfb) /\
                    U64.v nrw == U64.v crw + U64.v res.lead_rw)
          (ensures merge_inv g bs rest h nfb nrw fp)
  = reveal_opaque (`%merge_inv) merge_inv
#pop-options

/// A segment with a survivor: the joined run flushed to (h1, fp1), the first
/// link patched to (h2, fp2), the carry becomes its trailing run.
#push-options "--fuel 2 --ifuel 1"
let merge_used (g: heap_state) (bs: list nat) (r: SP.seg) (rest: list SP.seg)
    (h: heap_state) (cfb crw fp: U64.t) (res: seg_result) (rfb rrw: U64.t)
    (h1: heap_state) (fp1: U64.t) (h2: heap_state) (fp2: U64.t)
  : Lemma (requires merge_inv g bs (r :: rest) h cfb crw fp /\ result_matches res r.SP.out /\
                    res.all_free == false /\
                    rfb == (if U64.v crw = 0 then res.lead_fb else cfb) /\
                    U64.v rrw == U64.v crw + U64.v res.lead_rw /\
                    (h1, fp1) == SC.flush_blue h rfb (U64.v rrw) fp /\
                    (if res.has_link
                     then h2 == SP.patch_link h1 res.first_link fp1 /\ fp2 == res.local_head
                     else h2 == h1 /\ fp2 == fp1))
          (ensures merge_inv g bs rest h2 res.trail_fb res.trail_rw fp2)
  = reveal_opaque (`%merge_inv) merge_inv
#pop-options

/// No segments left: the last flush is the model's result.
#push-options "--fuel 1 --ifuel 1"
let merge_exit (g: heap_state) (bs: list nat) (h: heap_state) (cfb crw fp: U64.t)
  : Lemma (requires merge_inv g bs [] h cfb crw fp)
          (ensures run_ok cfb crw /\
                   SC.flush_blue h cfb (U64.v crw) fp == SP.sweep_par bs g)
  = reveal_opaque (`%merge_inv) merge_inv;
    pow2_57 ()
#pop-options

/// ---------------------------------------------------------------------------
/// Patching a link word
/// ---------------------------------------------------------------------------

let patch_yes (s: heap_state) (a v: U64.t)
  : Lemma (requires U64.v a >= 8 /\ U64.v a < heap_size /\ U64.v a % 8 == 0 /\
                    U64.v a + 8 <= heap_size)
          (ensures SP.patch_link s a v == SpecHeap.write_word s (a <: hp_addr) v)
  = let o : Base.obj_addr = a in
    SpecHeap.hd_address_spec o;
    CL.set_field_1_eq_write_word s o v

let patch_no (s: heap_state) (a v: U64.t)
  : Lemma (requires ~(U64.v a >= 8 /\ U64.v a < heap_size /\ U64.v a % 8 == 0 /\
                      U64.v a + 8 <= heap_size))
          (ensures SP.patch_link s a v == s)
  = if U64.v a >= 8 && U64.v a < heap_size && U64.v a % 8 = 0 then
      SpecHeap.hd_address_spec (a <: Base.obj_addr)

/// Set block a's link word to v, under the model's own guard.
fn patch (heap: heap_t) (a v: U64.t) (#s: erased heap_state)
  requires is_heap heap s
  ensures is_heap heap (SP.patch_link s a v)
{
  if (U64.gte a 8UL && U64.lt a heap_size_u64 &&
      U64.eq (U64.rem a 8UL) 0UL && U64.lte (U64.add a 8UL) heap_size_u64) {
    patch_yes s a v;
    let aa : hp_addr = a;
    write_word heap aa v;
    rewrite (is_heap heap (SpecHeap.write_word s aa v)) as (is_heap heap (SP.patch_link s a v))
  } else {
    patch_no s a v;
    rewrite (is_heap heap s) as (is_heap heap (SP.patch_link s a v))
  }
}

/// ---------------------------------------------------------------------------
/// The merge
/// ---------------------------------------------------------------------------

fn merge
  (heap: heap_t)
  (results: A.array seg_result)
  (m: SZ.t)
  (#g: erased heap_state)
  (#bs: erased (list nat))
  (#rs: erased (Seq.seq seg_result))
  (#p: perm)
  requires is_heap heap (SP.splice_all g (SP.sweep_all g (SP.segments bs))) **
           A.pts_to results #p rs **
           pure (SP.fused_pre g /\
                 SP.valid_bounds g bs /\
                 results_match rs (SZ.v m) (SP.sweep_all g (SP.segments bs)))
  returns fp: U64.t
  ensures exists* h.
    is_heap heap h **
    A.pts_to results #p rs **
    pure ((h, fp) == SP.sweep_par bs g)
{
  merge_entry g bs;
  let mut i = 0sz;
  let mut cfb = 0UL;
  let mut crw = 0UL;
  let mut fpr = 0UL;

  while (SZ.lt !i m)
    invariant exists* vi cf cr f h.
      pts_to i vi ** pts_to cfb cf ** pts_to crw cr ** pts_to fpr f **
      is_heap heap h ** A.pts_to results #p rs **
      pure (SZ.v vi <= SZ.v m /\
            results_match rs (SZ.v m) (SP.sweep_all g (SP.segments bs)) /\
            merge_inv g bs (drop (SP.sweep_all g (SP.segments bs)) (SZ.v vi)) h cf cr f)
    decreases (SZ.v m - SZ.v !i)
  {
    let vi = !i;
    let cf = !cfb;
    let cr = !crw;
    let f = !fpr;
    with h. assert (is_heap heap h);
    let all = Ghost.hide (SP.sweep_all g (SP.segments bs));
    drop_cons all (SZ.v vi);
    let r = Ghost.hide (List.Tot.index all (SZ.v vi));
    let rest = Ghost.hide (drop all (SZ.v vi + 1));
    let res = results.(vi);
    merge_head g bs r rest h cf cr f res;
    let rfb = (if U64.eq cr 0UL then res.lead_fb else cf);
    let rrw = U64.add cr res.lead_rw;
    if (res.all_free) {
      merge_free g bs r rest h cf cr f res rfb rrw;
      cfb := rfb;
      crw := rrw;
      i := SZ.add vi 1sz
    } else {
      let fl = Coalesce.flush_blue_impl heap rfb rrw f;
      let fp1 = snd fl;
      with h1. assert (is_heap heap h1);
      if (res.has_link) {
        patch heap res.first_link fp1;
        merge_used g bs r rest h cf cr f res rfb rrw h1 fp1
          (SP.patch_link h1 res.first_link fp1) res.local_head;
        fpr := res.local_head;
        cfb := res.trail_fb;
        crw := res.trail_rw;
        i := SZ.add vi 1sz
      } else {
        merge_used g bs r rest h cf cr f res rfb rrw h1 fp1 h1 fp1;
        fpr := fp1;
        cfb := res.trail_fb;
        crw := res.trail_rw;
        i := SZ.add vi 1sz
      }
    }
  };

  let cf = !cfb;
  let cr = !crw;
  let f = !fpr;
  with h. assert (is_heap heap h);
  drop_all (SP.sweep_all g (SP.segments bs)) (SZ.v m);
  merge_exit g bs h cf cr f;
  let fl = Coalesce.flush_blue_impl heap cf cr f;
  snd fl
}

/// ---------------------------------------------------------------------------
/// Non-vacuity
/// ---------------------------------------------------------------------------

/// The whole heap as one segment, with its record built from the model's
/// output: the lemmas above, called in the order merge calls them, on
/// arguments meeting their preconditions.  Which of merge_free and
/// merge_used applies depends on the heap; the record's construction is
/// guarded by its runs fitting a U64, which out_geom ensures.
#push-options "--fuel 2 --ifuel 1"
let merge_witness (g: heap_state) (a v: U64.t) : unit =
  let bs = [U64.v Base.zero_addr; heap_size] in
  SP.whole_heap_bounds_valid g;
  merge_entry g bs;
  let all = SP.sweep_all g (SP.segments bs) in
  let h = SP.splice_all g all in
  drop_cons all 0;
  drop_all all 1;
  let r = List.Tot.index all 0 in
  let o = r.SP.out in
  if o.SP.lead.SP.rw < pow2 64 && o.SP.trail.SP.rw < pow2 64 then begin
    let res = Mkseg_result o.SP.all_free
                o.SP.lead.SP.fb (U64.uint_to_t o.SP.lead.SP.rw)
                o.SP.trail.SP.fb (U64.uint_to_t o.SP.trail.SP.rw)
                (Some? o.SP.first_link)
                (match o.SP.first_link with Some x -> x | None -> 0UL)
                o.SP.local_head in
    merge_head g bs r [] h 0UL 0UL 0UL res;
    let rw = U64.uint_to_t o.SP.lead.SP.rw in
    if o.SP.all_free then begin
      merge_free g bs r [] h 0UL 0UL 0UL res res.lead_fb rw;
      merge_exit g bs h res.lead_fb rw 0UL
    end else begin
      let (h1, fp1) = SC.flush_blue h res.lead_fb (U64.v rw) 0UL in
      let h2 = if res.has_link then SP.patch_link h1 res.first_link fp1 else h1 in
      let fp2 = if res.has_link then res.local_head else fp1 in
      merge_used g bs r [] h 0UL 0UL 0UL res res.lead_fb rw h1 fp1 h2 fp2;
      merge_exit g bs h2 res.trail_fb res.trail_rw fp2
    end
  end;
  if U64.v a >= 8 && U64.v a < heap_size && U64.v a % 8 = 0 && U64.v a + 8 <= heap_size
  then patch_yes g a v
  else patch_no g a v
#pop-options
