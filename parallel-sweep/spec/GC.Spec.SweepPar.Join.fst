/// ---------------------------------------------------------------------------
/// GC.Spec.SweepPar.Join — the workers' ranges, put back together (proof)
///
/// Under valid_bounds, the segments of `sweep_all` tile [zero_addr,
/// heap_size): the first starts at zero_addr, each starts where the last
/// ended, and the last ends at heap_size.  Splicing such a list into any
/// heap keeps the heap's bytes below the first start and replaces the rest
/// with the segments' ranges, in order.  This is pure reasoning about
/// sequences; nothing about the sweep is used.
/// ---------------------------------------------------------------------------
module GC.Spec.SweepPar.Join

open FStar.Seq
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
module SP = GC.Spec.SweepPar

/// `rs` covers [lo0, heap_size) with no gap or overlap.
let rec tiles (lo0: nat) (rs: list SP.seg) : Tot prop (decreases rs) =
  match rs with
  | [] -> lo0 == heap_size
  | r :: rest -> r.SP.lo == lo0 /\ tiles r.SP.hi rest

/// The segments of a valid boundary list, from boundary `prev` on, tile
/// [prev, heap_size).
#push-options "--z3rlimit 20 --fuel 2 --ifuel 1"
let rec bounds_tile (g: heap) (prev: nat) (bs: list nat)
  : Lemma (requires SP.bounds_from g prev bs /\ prev % 8 == 0)
          (ensures tiles prev (SP.sweep_all g (SP.segments (prev :: bs))))
          (decreases bs)
  = match bs with
    | [b] -> ()
    | b :: rest -> bounds_tile g b rest
#pop-options

/// Splicing segment [lo, hi) leaves [0, lo) as `base` and [lo, hi) as `src`.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let splice_prefix (base src: heap) (lo: nat) (hi: nat{lo <= hi /\ hi <= heap_size})
  : Lemma (Seq.slice (SP.splice base src lo hi) 0 hi ==
           Seq.append (Seq.slice base 0 lo) (Seq.slice src lo hi))
  = let a = Seq.slice base 0 lo in
    let b = Seq.slice src lo hi in
    let c = Seq.slice base hi heap_size in
    Seq.append_assoc a b c;
    Seq.lemma_eq_intro (Seq.slice (Seq.append (Seq.append a b) c) 0 hi) (Seq.append a b)
#pop-options

/// Splicing a tiling of [lo0, heap_size) into `h`: h's bytes below lo0, then
/// the segments' ranges.
#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
let rec splice_tiles (h: heap) (lo0: nat{lo0 <= heap_size}) (rs: list SP.seg)
  : Lemma (requires tiles lo0 rs)
          (ensures Seq.append (Seq.slice h 0 lo0) (seg_bytes rs) == SP.splice_all h rs)
          (decreases rs)
  = match rs with
    | [] -> Seq.append_empty_r (Seq.slice h 0 lo0);
            Seq.lemma_eq_intro (Seq.slice h 0 heap_size) h
    | r :: rest ->
      let h' = SP.splice h r.SP.out.SP.sheap r.SP.lo r.SP.hi in
      splice_tiles h' r.SP.hi rest;
      splice_prefix h r.SP.out.SP.sheap r.SP.lo r.SP.hi;
      Seq.append_assoc (Seq.slice h 0 lo0)
                       (Seq.slice r.SP.out.SP.sheap r.SP.lo r.SP.hi)
                       (seg_bytes rest)
#pop-options

#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
let join_correct g bs =
  match bs with
  | b0 :: rest ->
    bounds_tile g b0 rest;
    splice_tiles g (U64.v zero_addr) (SP.sweep_all g (SP.segments bs))
#pop-options

/// ---------------------------------------------------------------------------
/// Non-vacuity
/// ---------------------------------------------------------------------------

/// Every heap meets the hypothesis with the whole heap as one segment
/// (SP.whole_heap_bounds_valid).  Through this call, `bounds_tile` (its
/// last-boundary case), `splice_tiles` (both cases) and `splice_prefix` are
/// called on arguments meeting their preconditions.
let join_witness (g: heap) : unit =
  SP.whole_heap_bounds_valid g;
  join_correct g [U64.v zero_addr; heap_size]

/// Two segments, cut at a walk position `b`: `bounds_tile`'s recursive case.
/// Guarded by the heap's shape; the tests build heaps meeting it.
let join_witness_two (g: heap) (b: nat) : unit =
  if SP.valid_bounds g [U64.v zero_addr; b; heap_size]
  then join_correct g [U64.v zero_addr; b; heap_size]
