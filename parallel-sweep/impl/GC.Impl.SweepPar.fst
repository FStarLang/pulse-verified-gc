(*
   Pulse GC - Parallel sweep: pre-pass, merge, and a sequential driver

   prepass and merge are implemented in GC.Impl.SweepPar.Prepass and
   GC.Impl.SweepPar.Merge, with this interface's signatures; they are
   separate modules so that each could be verified before this one, which
   needs all three functions, existed.  This module gives each its interface
   name, and implements sweep_par_seq from them and sweep_segment.

   sweep_par_seq, in one thread:
     1. prepass writes n boundaries b0 = zero_addr < b1 < ... < b(n-1) = heap_size;
     2. the heap is cut into [0, zero_addr) and the rest; for each segment
        in turn, the rest is cut at the segment's end, sweep_segment runs on
        the segment's range alone, and the range is joined back onto the
        part already swept;
     3. by GC.Spec.SweepPar.Join.join_correct, the joined heap is the model's
        splice_all g rs, which is merge's precondition;
     4. merge gives sweep_par bs g, which GC.Spec.SweepPar.sweep_par_correct
        equates with fused_sweep_coalesce g.
*)

module GC.Impl.SweepPar

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsToRange
open GC.Impl.Heap
open GC.Impl.SweepSegment
module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module Seq = FStar.Seq
module Base = GC.Spec.Base
module SP = GC.Spec.SweepPar
module SL = GC.Spec.SweepPar.SegLoop
module J = GC.Spec.SweepPar.Join
module Defs = GC.Spec.SweepCoalesce.Defs
module PP = GC.Impl.SweepPar.Prepass
module MG = GC.Impl.SweepPar.Merge

/// ---------------------------------------------------------------------------
/// 1. The pre-pass
/// ---------------------------------------------------------------------------

fn prepass
  (heap: heap_t)
  (k: SZ.t{SZ.v k >= 1})
  (bounds: A.array U64.t)
  (#g: erased heap_state)
  (#s0: erased (Seq.seq U64.t))
  requires is_heap heap g **
           A.pts_to bounds s0 **
           pure (A.length bounds == SZ.v k + 1)
  returns n: SZ.t
  ensures exists* s.
    is_heap heap g **
    A.pts_to bounds s **
    pure (Seq.length s == SZ.v k + 1 /\
          2 <= SZ.v n /\ SZ.v n <= SZ.v k + 1 /\
          SP.valid_bounds g (bounds_list s (SZ.v n)))
{
  PP.prepass heap k bounds
}

/// ---------------------------------------------------------------------------
/// 3. The merge
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
  MG.merge heap results m
}

/// ---------------------------------------------------------------------------
/// The segments of the boundary array
/// ---------------------------------------------------------------------------

/// Pair j of the entries i .. n - 1 is (s[j], s[j + 1]).
#push-options "--fuel 2 --ifuel 1"
let rec idx_seg_mem (s: Seq.seq U64.t) (n: nat{n <= Seq.length s}) (i j: nat)
  : Lemma (requires i <= j /\ j + 1 < n)
          (ensures List.Tot.memP (U64.v (Seq.index s j), U64.v (Seq.index s (j + 1)))
                                 (SP.segments (PP.idx_list s i n)))
          (decreases (j - i))
  = if i = j then () else idx_seg_mem s n (i + 1) j
#pop-options

/// A segment of a valid list is an aligned, in-range, non-empty pair.
let seg_bounds (g: heap_state) (bs: list nat) (lo hi: nat)
  : Lemma (requires SP.valid_bounds g bs /\ List.Tot.memP (lo, hi) (SP.segments bs))
          (ensures lo < hi /\ hi <= heap_size /\ lo % 8 == 0 /\ lo < heap_size)
  = match bs with
    | b0 :: rest ->
      assert (Base.mk_hp_addr b0 == Base.zero_addr);
      SL.seg_mem_reach g b0 rest lo hi

/// The array's first n entries, as the model's list.
let bounds_idx (s: Seq.seq U64.t) (n: nat{n <= Seq.length s})
  : Lemma (bounds_list s n == PP.idx_list s 0 n)
  = PP.slice_list s 0 n

/// sweep_all over the pairs from i on: n - 1 - i segments, the j-th of
/// them built from (s[i + j], s[i + j + 1]).
#push-options "--fuel 2 --ifuel 1"
let rec sweep_all_len (g: heap_state) (s: Seq.seq U64.t) (n: nat{n <= Seq.length s}) (i: nat)
  : Lemma (requires SP.valid_bounds g (bounds_list s n) /\ i < n)
          (ensures List.Tot.length (SP.sweep_all g (SP.segments (PP.idx_list s i n))) == n - 1 - i)
          (decreases (n - i))
  = if i + 1 = n then ()
    else begin
      bounds_idx s n;
      idx_seg_mem s n 0 i;
      seg_bounds g (bounds_list s n) (U64.v (Seq.index s i)) (U64.v (Seq.index s (i + 1)));
      sweep_all_len g s n (i + 1)
    end

let rec sweep_all_index (g: heap_state) (s: Seq.seq U64.t) (n: nat{n <= Seq.length s}) (i j: nat)
  : Lemma (requires SP.valid_bounds g (bounds_list s n) /\ i <= j /\ j + 1 < n)
          (ensures (let l = SP.sweep_all g (SP.segments (PP.idx_list s i n)) in
                    j - i < List.Tot.length l /\
                    U64.v (Seq.index s j) < heap_size /\ U64.v (Seq.index s j) % 8 == 0 /\
                    (let r = List.Tot.index l (j - i) in
                     r.SP.lo == U64.v (Seq.index s j) /\
                     r.SP.hi == U64.v (Seq.index s (j + 1)) /\
                     r.SP.out == SP.sweep_segment g (U64.uint_to_t (U64.v (Seq.index s j)))
                                   (U64.v (Seq.index s (j + 1))))))
          (decreases (j - i))
  = bounds_idx s n;
    idx_seg_mem s n 0 i;
    seg_bounds g (bounds_list s n) (U64.v (Seq.index s i)) (U64.v (Seq.index s (i + 1)));
    sweep_all_len g s n i;
    idx_seg_mem s n 0 j;
    seg_bounds g (bounds_list s n) (U64.v (Seq.index s j)) (U64.v (Seq.index s (j + 1)));
    if i = j then ()
    else sweep_all_index g s n (i + 1) j
#pop-options

/// What the driver needs to know about segment j.
let seg_facts (g: heap_state) (s: Seq.seq U64.t) (n: nat{n <= Seq.length s}) (j: nat)
  : Lemma (requires SP.valid_bounds g (bounds_list s n) /\ j + 1 < n)
          (ensures (let bs = bounds_list s n in
                    let all = SP.sweep_all g (SP.segments bs) in
                    let lo = U64.v (Seq.index s j) in
                    let hi = U64.v (Seq.index s (j + 1)) in
                    lo < hi /\ hi <= heap_size /\ lo % 8 == 0 /\ lo < heap_size /\
                    List.Tot.memP (lo, hi) (SP.segments bs) /\
                    List.Tot.length all == n - 1 /\
                    j < List.Tot.length all /\
                    (List.Tot.index all j).SP.lo == lo /\
                    (List.Tot.index all j).SP.hi == hi /\
                    (List.Tot.index all j).SP.out ==
                      SP.sweep_segment g (U64.uint_to_t lo) hi))
  = bounds_idx s n;
    idx_seg_mem s n 0 j;
    seg_bounds g (bounds_list s n) (U64.v (Seq.index s j)) (U64.v (Seq.index s (j + 1)));
    sweep_all_len g s n 0;
    sweep_all_index g s n 0 j

/// The first and last boundaries.
#push-options "--fuel 2 --ifuel 1"
let rec idx_last (g: heap_state) (s: Seq.seq U64.t) (n: nat{n <= Seq.length s}) (i: nat) (prev: nat)
  : Lemma (requires i < n /\ SP.bounds_from g prev (PP.idx_list s i n))
          (ensures U64.v (Seq.index s (n - 1)) == heap_size)
          (decreases (n - i))
  = if i + 1 = n then () else idx_last g s n (i + 1) (U64.v (Seq.index s i))
#pop-options

#push-options "--fuel 1 --ifuel 1"
let ends (g: heap_state) (s: Seq.seq U64.t) (n: nat{n <= Seq.length s})
  : Lemma (requires SP.valid_bounds g (bounds_list s n) /\ 2 <= n)
          (ensures U64.v (Seq.index s 0) == U64.v zero_addr /\
                   U64.v (Seq.index s (n - 1)) == heap_size)
  = bounds_idx s n;
    idx_last g s n 1 (U64.v (Seq.index s 0))
#pop-options

/// ---------------------------------------------------------------------------
/// The heap, put back together segment by segment
/// ---------------------------------------------------------------------------

let rec take (l: list SP.seg) (j: nat) : Tot (list SP.seg) (decreases l) =
  if j = 0 then [] else match l with [] -> [] | x :: t -> x :: take t (j - 1)

/// The bytes the driver holds below the current boundary after j segments:
/// those below zero_addr, then each swept segment's range.
let done_bytes (g: heap_state) (all: list SP.seg) (j: nat) : Seq.seq U8.t =
  Seq.append (Seq.slice g 0 (U64.v zero_addr)) (J.seg_bytes (take all j))

let seg_range (r: SP.seg) : Seq.seq U8.t = Seq.slice r.SP.out.SP.sheap r.SP.lo r.SP.hi

#push-options "--fuel 2 --ifuel 1"
let rec seg_bytes_snoc (l: list SP.seg) (j: nat)
  : Lemma (requires j < List.Tot.length l)
          (ensures J.seg_bytes (take l (j + 1)) ==
                   Seq.append (J.seg_bytes (take l j)) (seg_range (List.Tot.index l j)))
          (decreases l)
  = match l with
    | x :: t ->
      if j = 0 then begin
        Seq.append_empty_r (seg_range x);
        Seq.append_empty_l (seg_range x)
      end else begin
        seg_bytes_snoc t (j - 1);
        Seq.append_assoc (seg_range x) (J.seg_bytes (take t (j - 1)))
                         (seg_range (List.Tot.index t (j - 1)))
      end

let rec take_length (l: list SP.seg) (j: nat)
  : Lemma (requires j >= List.Tot.length l) (ensures take l j == l) (decreases l)
  = match l with [] -> () | _ :: t -> take_length t (j - 1)
#pop-options

let done_start (g: heap_state) (all: list SP.seg)
  : Lemma (done_bytes g all 0 == Seq.slice g 0 (U64.v zero_addr))
  = Seq.append_empty_r (Seq.slice g 0 (U64.v zero_addr))

let done_step (g: heap_state) (all: list SP.seg) (j: nat)
  : Lemma (requires j < List.Tot.length all)
          (ensures done_bytes g all (j + 1) ==
                   Seq.append (done_bytes g all j) (seg_range (List.Tot.index all j)))
  = seg_bytes_snoc all j;
    Seq.append_assoc (Seq.slice g 0 (U64.v zero_addr)) (J.seg_bytes (take all j))
                     (seg_range (List.Tot.index all j))

/// After every segment, the bytes are the model's spliced heap.
let done_end (g: heap_state) (bs: list nat)
  : Lemma (requires SP.valid_bounds g bs)
          (ensures (let all = SP.sweep_all g (SP.segments bs) in
                    Seq.append (done_bytes g all (List.Tot.length all))
                               (Seq.slice g heap_size heap_size) ==
                    SP.splice_all g all))
  = let all = SP.sweep_all g (SP.segments bs) in
    take_length all (List.Tot.length all);
    J.join_correct g bs;
    Seq.append_empty_r (done_bytes g all (List.Tot.length all));
    assert (Seq.equal (Seq.slice g heap_size heap_size) Seq.empty)

/// Cutting the unswept part [lo, heap_size) at hi.
let cut_rest (g: heap_state) (lo hi: nat)
  : Lemma (requires lo <= hi /\ hi <= heap_size)
          (ensures Seq.slice (Seq.slice g lo heap_size) 0 (hi - lo) == Seq.slice g lo hi /\
                   Seq.slice (Seq.slice g lo heap_size) (hi - lo) (heap_size - lo) ==
                     Seq.slice g hi heap_size)
  = Seq.lemma_eq_intro (Seq.slice (Seq.slice g lo heap_size) 0 (hi - lo)) (Seq.slice g lo hi);
    Seq.lemma_eq_intro (Seq.slice (Seq.slice g lo heap_size) (hi - lo) (heap_size - lo))
                       (Seq.slice g hi heap_size)

/// Boundary j, and the unswept bytes from b: total, so the loop invariant
/// is well typed before its pure facts are known.
let at (s: Seq.seq U64.t) (j: nat) : nat =
  if j < Seq.length s then U64.v (Seq.index s j) else 0

let tail_of (g: heap_state) (b: nat) : Seq.seq U8.t =
  if b <= heap_size then Seq.slice g b heap_size else Seq.empty

/// The records written so far match the model's outputs.
let recs_ok (rq: Seq.seq seg_result) (all: list SP.seg) (j: nat) : prop =
  j <= Seq.length rq /\ j <= List.Tot.length all /\
  (forall (i: nat). i < j ==> result_matches (Seq.index rq i) (List.Tot.index all i).SP.out)

/// ---------------------------------------------------------------------------
/// The three steps in one thread
/// ---------------------------------------------------------------------------

/// Sweep segment j: cut its range off the unswept part, sweep it, and join
/// it onto the swept part.
fn sweep_one
  (heap: heap_t)
  (lo: hp_addr)
  (hi: U64.t{U64.v lo < U64.v hi /\ U64.v hi <= heap_size})
  (#g: erased heap_state)
  (#bs: erased (list nat))
  (#pre: erased (Seq.seq U8.t))
  requires pts_to_range heap.data 0 (U64.v lo) pre **
           pts_to_range heap.data (U64.v lo) heap_size (Seq.slice g (U64.v lo) heap_size) **
           pure (SP.fused_pre g /\
                 SP.valid_bounds g bs /\
                 List.Tot.memP (U64.v lo, U64.v hi) (SP.segments bs))
  returns r: seg_result
  ensures pts_to_range heap.data 0 (U64.v hi)
            (Seq.append pre (Seq.slice (SP.sweep_segment g lo (U64.v hi)).SP.sheap
                                       (U64.v lo) (U64.v hi))) **
          pts_to_range heap.data (U64.v hi) heap_size (Seq.slice g (U64.v hi) heap_size) **
          pure (result_matches r (SP.sweep_segment g lo (U64.v hi)))
{
  pts_to_range_split heap.data (U64.v lo) (U64.v hi) heap_size;
  cut_rest g (U64.v lo) (U64.v hi);
  with s1 s2. assert (pts_to_range heap.data (U64.v lo) (U64.v hi) s1 **
                      pts_to_range heap.data (U64.v hi) heap_size s2);
  rewrite (pts_to_range heap.data (U64.v lo) (U64.v hi) s1)
       as (is_heap_range heap (U64.v lo) (U64.v hi) (Seq.slice g (U64.v lo) (U64.v hi)));
  rewrite (pts_to_range heap.data (U64.v hi) heap_size s2)
       as (pts_to_range heap.data (U64.v hi) heap_size (Seq.slice g (U64.v hi) heap_size));
  let r = sweep_segment heap lo hi #g #bs;
  with s. assert (is_heap_range heap (U64.v lo) (U64.v hi) s);
  unfold is_heap_range;
  pts_to_range_join heap.data 0 (U64.v lo) (U64.v hi);
  r
}

fn sweep_par_seq
  (heap: heap_t)
  (k: SZ.t{SZ.v k >= 1})
  (bounds: A.array U64.t)
  (results: A.array seg_result)
  (#g: erased heap_state)
  (#b0: erased (Seq.seq U64.t))
  (#r0: erased (Seq.seq seg_result))
  requires is_heap heap g **
           A.pts_to bounds b0 **
           A.pts_to results r0 **
           pure (A.length bounds == SZ.v k + 1 /\
                 A.length results == SZ.v k /\
                 SP.fused_pre g)
  returns fp: U64.t
  ensures exists* h b r.
    is_heap heap h **
    A.pts_to bounds b **
    A.pts_to results r **
    pure ((h, fp) == Defs.fused_sweep_coalesce g)
{
  // 1. The boundaries.
  let n = prepass heap k bounds;
  with s. assert (A.pts_to bounds s);
  let bs : erased (list nat) = hide (bounds_list s (SZ.v n));
  let all : erased (list SP.seg) = hide (SP.sweep_all g (SP.segments bs));
  ends g s (SZ.v n);
  sweep_all_len g s (SZ.v n) 0;
  bounds_idx s (SZ.v n);
  A.pts_to_len results;

  // 2. The heap as [0, zero_addr) and [zero_addr, heap_size).
  unfold is_heap;
  A.pts_to_len heap.data;
  pts_to_range_intro heap.data 1.0R g;
  pts_to_range_split heap.data 0 (U64.v zero_addr) heap_size;
  with p1 p2. assert (pts_to_range heap.data 0 (U64.v zero_addr) p1 **
                      pts_to_range heap.data (U64.v zero_addr) heap_size p2);
  done_start g all;
  rewrite (pts_to_range heap.data 0 (U64.v zero_addr) p1)
       as (pts_to_range heap.data 0 (at s 0) (done_bytes g all 0));
  rewrite (pts_to_range heap.data (U64.v zero_addr) heap_size p2)
       as (pts_to_range heap.data (at s 0) heap_size (tail_of g (at s 0)));

  // 3. Each segment in turn.
  let m = SZ.sub n 1sz;
  let mut j = 0sz;
  while (SZ.lt !j m)
    invariant exists* vj rq.
      pts_to j vj **
      A.pts_to bounds s **
      A.pts_to results rq **
      pts_to_range heap.data 0 (at s (SZ.v vj)) (done_bytes g all (SZ.v vj)) **
      pts_to_range heap.data (at s (SZ.v vj)) heap_size (tail_of g (at s (SZ.v vj))) **
      pure (SZ.v vj <= SZ.v m /\
            Seq.length s == SZ.v k + 1 /\ 2 <= SZ.v n /\ SZ.v n <= SZ.v k + 1 /\
            SP.valid_bounds g bs /\ SP.fused_pre g /\
            bs == bounds_list s (SZ.v n) /\
            all == SP.sweep_all g (SP.segments bs) /\
            List.Tot.length all == SZ.v m /\
            U64.v (Seq.index s (SZ.v n - 1)) == heap_size /\
            Seq.length rq == SZ.v k /\
            recs_ok rq all (SZ.v vj))
    decreases (SZ.v m - SZ.v !j)
  {
    let vj = !j;
    seg_facts g s (SZ.v n) (SZ.v vj);
    let vj1 = SZ.add vj 1sz;
    let lo_w = bounds.(vj);
    let hi = bounds.(vj1);
    let lo : hp_addr = lo_w;
    rewrite (pts_to_range heap.data 0 (at s (SZ.v vj)) (done_bytes g all (SZ.v vj)))
         as (pts_to_range heap.data 0 (U64.v lo) (done_bytes g all (SZ.v vj)));
    rewrite (pts_to_range heap.data (at s (SZ.v vj)) heap_size (tail_of g (at s (SZ.v vj))))
         as (pts_to_range heap.data (U64.v lo) heap_size (Seq.slice g (U64.v lo) heap_size));
    let r = sweep_one heap lo hi #g #bs;
    done_step g all (SZ.v vj);
    rewrite (pts_to_range heap.data 0 (U64.v hi)
               (Seq.append (done_bytes g all (SZ.v vj))
                  (Seq.slice (SP.sweep_segment g lo (U64.v hi)).SP.sheap (U64.v lo) (U64.v hi))))
         as (pts_to_range heap.data 0 (at s (SZ.v vj1)) (done_bytes g all (SZ.v vj1)));
    rewrite (pts_to_range heap.data (U64.v hi) heap_size (Seq.slice g (U64.v hi) heap_size))
         as (pts_to_range heap.data (at s (SZ.v vj1)) heap_size
               (tail_of g (at s (SZ.v vj1))));
    results.(vj) <- r;
    j := vj1
  };

  // 4. The whole heap again: the model's spliced heap.
  with vj. assert (pts_to j vj);
  rewrite (pts_to_range heap.data 0 (at s (SZ.v vj)) (done_bytes g all (SZ.v vj)))
       as (pts_to_range heap.data 0 heap_size (done_bytes g all (List.Tot.length all)));
  rewrite (pts_to_range heap.data (at s (SZ.v vj)) heap_size (tail_of g (at s (SZ.v vj))))
       as (pts_to_range heap.data heap_size heap_size (Seq.slice g heap_size heap_size));
  pts_to_range_join heap.data 0 heap_size heap_size;
  done_end g bs;
  rewrite (pts_to_range heap.data 0 heap_size
             (Seq.append (done_bytes g all (List.Tot.length all)) (Seq.slice g heap_size heap_size)))
       as (pts_to_range heap.data 0 (A.length heap.data) (SP.splice_all g all));
  pts_to_range_elim heap.data 1.0R (SP.splice_all g all);
  fold (is_heap heap (SP.splice_all g all));
  rewrite (is_heap heap (SP.splice_all g all))
       as (is_heap heap (SP.splice_all g (SP.sweep_all g (SP.segments bs))));

  // 5. Link, and the theorem.
  let fp = merge heap results m #g #bs;
  SP.sweep_par_correct bs g;
  fp
}

/// ---------------------------------------------------------------------------
/// Non-vacuity
/// ---------------------------------------------------------------------------

/// The pure lemmas above, on arguments meeting their preconditions: the
/// boundary array [zero_addr; heap_size], valid on every heap, and, when the
/// heap has a walk position b, [zero_addr; b; heap_size], which reaches
/// the recursive cases.
#push-options "--fuel 3 --ifuel 1"
let driver_witness (g: heap_state) (b: U64.t) : unit =
  let s = Seq.append (Seq.create 1 zero_addr) (Seq.create 1 heap_size_u64) in
  bounds_idx s 2;
  assert (Seq.index s 0 == zero_addr /\ Seq.index s 1 == heap_size_u64);
  assert (PP.idx_list s 0 2 == [U64.v zero_addr; heap_size]);
  SP.whole_heap_bounds_valid g;
  seg_facts g s 2 0;
  ends g s 2;
  let bs = bounds_list s 2 in
  let all = SP.sweep_all g (SP.segments bs) in
  done_start g all;
  done_step g all 0;
  seg_bytes_snoc all 0;
  take_length all 1;
  done_end g bs;
  cut_rest g (U64.v zero_addr) heap_size;
  let s3 = Seq.append (Seq.create 1 zero_addr)
             (Seq.append (Seq.create 1 b) (Seq.create 1 heap_size_u64)) in
  if SP.valid_bounds g (bounds_list s3 3) then begin
    seg_facts g s3 3 1;
    ends g s3 3
  end
#pop-options
