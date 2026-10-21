/// ---------------------------------------------------------------------------
/// GC.Spec.SweepPar.Join — the workers' ranges, put back together
///
/// Statement only; the proof is not written yet.
///
/// Each worker gives back the bytes [lo, hi) of its segment's copy of the
/// heap (GC.Impl.SweepSegment.sweep_segment).  The bytes below zero_addr
/// belong to no segment and are never written.  Put back together left to
/// right, these pieces are the heap the model's merge step starts from:
/// `splice_all g rs`.
/// ---------------------------------------------------------------------------
module GC.Spec.SweepPar.Join

open FStar.Seq
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
module SP = GC.Spec.SweepPar

/// The bytes each segment keeps, [lo, hi) of its own copy, in order.
let rec seg_bytes (rs: list SP.seg) : seq U8.t =
  match rs with
  | [] -> Seq.empty
  | r :: rest ->
    Seq.append (Seq.slice r.SP.out.SP.sheap r.SP.lo r.SP.hi) (seg_bytes rest)

/// The bytes below zero_addr, then every segment's range, is the spliced heap.
val join_correct (g: heap) (bs: list nat)
  : Lemma (requires SP.valid_bounds g bs)
          (ensures (let rs = SP.sweep_all g (SP.segments bs) in
                    eq2 #(seq U8.t)
                      (Seq.append (Seq.slice g 0 (U64.v zero_addr)) (seg_bytes rs))
                      (SP.splice_all g rs)))
