/// ---------------------------------------------------------------------------
/// GC.Spec.SweepPar.Local — one segment depends only on its own bytes
///
/// If two heaps agree on [lo, hi), the model's `sweep_segment` gives the same
/// bytes in [lo, hi) and the same other outputs for both.  This is what lets
/// the Pulse `sweep_segment` (parallel-sweep/impl/GC.Impl.SweepSegment.fsti)
/// own only its range: it computes the model's segment from those bytes alone.
///
/// Why it holds: a segment reads only object headers whose address is in
/// [lo, hi) (the walk, the colour and size tests, and `makeWhite`'s re-read).
/// Every write (`makeWhite`, and all of `flush_blue`) writes the same value
/// at the same address in both runs, so it keeps the heaps in agreement on
/// [lo, hi), wherever it lands.  No other hypothesis is needed: not
/// `fused_pre`, and not that lo and hi are walk positions; only that hi is
/// word-aligned, so a header read below hi lies wholly below it.
/// ---------------------------------------------------------------------------
module GC.Spec.SweepPar.Local

open FStar.Seq
module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.SweepPar.Exec
open GC.Spec.SweepPar

/// ---------------------------------------------------------------------------
/// Agreement on a byte range
/// ---------------------------------------------------------------------------

let agree (h1 h2: heap) (lo hi: nat) : prop =
  forall (i: nat). lo <= i /\ i < hi /\ i < heap_size ==> Seq.index h1 i == Seq.index h2 i

let agree_of_slice (h1 h2: heap) (lo: nat) (hi: nat{lo <= hi /\ hi <= heap_size})
  : Lemma (requires Seq.slice h1 lo hi == Seq.slice h2 lo hi)
          (ensures agree h1 h2 lo hi)
  = let aux (i: nat) : Lemma (lo <= i /\ i < hi ==> Seq.index h1 i == Seq.index h2 i) =
      if lo <= i && i < hi then begin
        Seq.lemma_index_slice h1 lo hi (i - lo);
        Seq.lemma_index_slice h2 lo hi (i - lo)
      end in
    FStar.Classical.forall_intro aux

let slice_of_agree (h1 h2: heap) (lo: nat) (hi: nat{lo <= hi /\ hi <= heap_size})
  : Lemma (requires agree h1 h2 lo hi)
          (ensures Seq.slice h1 lo hi == Seq.slice h2 lo hi)
  = Seq.lemma_eq_intro (Seq.slice h1 lo hi) (Seq.slice h2 lo hi)

/// A word wholly inside the range reads the same in both heaps.
let read_agree (h1 h2: heap) (lo hi: nat) (a: hp_addr)
  : Lemma (requires agree h1 h2 lo hi /\ lo <= U64.v a /\ U64.v a + 8 <= hi)
          (ensures read_word h1 a == read_word h2 a)
  = read_word_spec h1 a;
    read_word_spec h2 a

/// The same write to both heaps keeps them in agreement, wherever it lands.
let write_agree (h1 h2: heap) (lo hi: nat) (a: hp_addr) (v: U64.t)
  : Lemma (requires agree h1 h2 lo hi)
          (ensures agree (write_word h1 a v) (write_word h2 a v) lo hi)
  = write_word_spec h1 a v;
    write_word_spec h2 a v

/// ---------------------------------------------------------------------------
/// The writes: makeWhite and flush_blue
/// ---------------------------------------------------------------------------

/// makeWhite re-reads the header it rewrites, so the header must be inside.
let makeWhite_agree (h1 h2: heap) (lo hi: nat) (x: obj_addr)
  : Lemma (requires agree h1 h2 lo hi /\
                    lo <= U64.v (hd_address x) /\ U64.v (hd_address x) + 8 <= hi)
          (ensures agree (makeWhite_x x h1) (makeWhite_x x h2) lo hi)
  = read_agree h1 h2 lo hi (hd_address x);
    write_agree h1 h2 lo hi (hd_address x)
      (colorHeader (read_word h1 (hd_address x)) GC.Lib.Header.White)

let rec zero_fields_agree (h1 h2: heap) (lo hi: nat) (addr: U64.t) (n: nat)
  : Lemma (requires agree h1 h2 lo hi)
          (ensures agree (zero_fields_x h1 addr n) (zero_fields_x h2 addr n) lo hi)
          (decreases n)
  = if n = 0 then ()
    else if U64.v addr + 8 > heap_size then ()
    else if U64.v addr >= heap_size then ()
    else if U64.v addr % 8 <> 0 then ()
    else begin
      write_agree h1 h2 lo hi (addr <: hp_addr) 0UL;
      if U64.v addr + 8 >= pow2 64 then ()
      else
        zero_fields_agree (write_word h1 (addr <: hp_addr) 0UL) (write_word h2 (addr <: hp_addr) 0UL)
          lo hi (U64.uint_to_t (U64.v addr + 8)) (n - 1)
    end

/// flush_blue only writes, with values fixed by its arguments: it keeps any
/// agreement, and returns the same head.
#push-options "--z3rlimit 40"
let flush_agree (h1 h2: heap) (lo hi: nat) (fb: U64.t) (rw: nat) (fp: U64.t)
  : Lemma (requires agree h1 h2 lo hi)
          (ensures agree (fst (flush_blue_x h1 fb rw fp)) (fst (flush_blue_x h2 fb rw fp)) lo hi /\
                   snd (flush_blue_x h1 fb rw fp) == snd (flush_blue_x h2 fb rw fp))
  = if rw = 0 then ()
    else if U64.v fb < U64.v mword || U64.v fb >= heap_size || U64.v fb % U64.v mword <> 0
    then ()
    else
      let fbo : obj_addr = fb in
      let hd = hd_address fbo in
      let wz = rw - 1 in
      if wz >= pow2 54 then ()
      else begin
        FStar.Math.Lemmas.pow2_lt_compat 64 54;
        let wz_u64 : wosize = U64.uint_to_t wz in
        let hdr = makeHeader wz_u64 GC.Lib.Header.Blue 0UL in
        write_agree h1 h2 lo hi hd hdr;
        let g1 = write_word h1 hd hdr in
        let g2 = write_word h2 hd hdr in
        if wz >= 1 && U64.v hd + U64.v mword * 2 <= heap_size then begin
          let fa : hp_addr = U64.add hd (U64.mul mword 1UL) in
          write_agree g1 g2 lo hi fa fp;
          let zero_start_nat = U64.v fbo + U64.v mword in
          if wz >= 2 && zero_start_nat < pow2 64 then
            zero_fields_agree (set_field_x g1 fbo 1UL fp) (set_field_x g2 fbo 1UL fp)
              lo hi (U64.uint_to_t zero_start_nat) (wz - 1)
          else ()
        end
        else ()
      end
#pop-options

/// ---------------------------------------------------------------------------
/// The walk
/// ---------------------------------------------------------------------------

/// Every object's header lies in [lo, hi).
let hdrs_in (objs: seq obj_addr) (lo hi: nat) : prop =
  forall (i: nat). i < Seq.length objs ==>
    lo <= U64.v (hd_address (Seq.index objs i)) /\
    U64.v (hd_address (Seq.index objs i)) + 8 <= hi

/// The segment's walk from `start` reads only headers in [start, hi), so it
/// is the same in both heaps, and lists only objects with headers there.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let rec seg_objects_agree (g1 g2: heap) (lo: nat) (start: hp_addr) (hi: nat)
  : Lemma (requires agree g1 g2 lo hi /\ lo <= U64.v start /\ hi % 8 == 0)
          (ensures seg_objects g1 start hi == seg_objects g2 start hi /\
                   hdrs_in (seg_objects g1 start hi) (U64.v start) hi)
          (decreases (heap_size - U64.v start))
  = if U64.v start >= hi then ()
    else if U64.v start + 8 >= heap_size then ()
    else begin
      read_agree g1 g2 lo hi start;
      let wz = getWosize (read_word g1 start) in
      let next = U64.v start + (U64.v wz + 1) * 8 in
      if next > heap_size || next >= pow2 64 then ()
      else begin
        f_address_spec start;
        hd_f_roundtrip start;
        let o : obj_addr = f_address start in
        if next >= heap_size then ()
        else begin
          aligned_plus_mul8 (U64.v start) (U64.v wz + 1);
          let nx = mk_hp_addr next in
          seg_objects_agree g1 g2 lo nx hi;
          let rest = seg_objects g1 nx hi in
          let s = Seq.cons o rest in
          let aux (i: nat) : Lemma (i < Seq.length s ==>
                U64.v start <= U64.v (hd_address (Seq.index s i)) /\
                U64.v (hd_address (Seq.index s i)) + 8 <= hi) =
            if i = 0 then ()
            else if i < Seq.length s then begin
              assert (Seq.index s i == Seq.index rest (i - 1));
              hd_address_spec (Seq.index rest (i - 1))
            end in
          FStar.Classical.forall_intro aux
        end
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// seg_aux, step by step
/// ---------------------------------------------------------------------------

let same_out (o1 o2: seg_out) (lo hi: nat) : prop =
  agree o1.sheap o2.sheap lo hi /\
  o1.all_free == o2.all_free /\ o1.lead == o2.lead /\ o1.trail == o2.trail /\
  o1.first_link == o2.first_link /\ o1.local_head == o2.local_head

#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let rec seg_aux_agree (g01 g02 h1 h2: heap) (lo hi: nat) (objs: seq obj_addr)
    (seen: bool) (lead cur: run) (fp: U64.t) (first: option U64.t)
  : Lemma (requires agree g01 g02 lo hi /\ agree h1 h2 lo hi /\ hdrs_in objs lo hi)
          (ensures same_out (seg_aux g01 h1 objs seen lead cur fp first)
                            (seg_aux g02 h2 objs seen lead cur fp first) lo hi)
          (decreases Seq.length objs)
  = if Seq.length objs = 0 then ()
    else begin
      let obj = Seq.head objs in
      let rest = Seq.tail objs in
      assert (obj == Seq.index objs 0);
      assert (forall (i: nat). i < Seq.length rest ==> Seq.index rest i == Seq.index objs (i + 1));
      read_agree g01 g02 lo hi (hd_address obj);
      if is_black_x obj g01 then
        if not seen then begin
          makeWhite_agree h1 h2 lo hi obj;
          seg_aux_agree g01 g02 (makeWhite_x obj h1) (makeWhite_x obj h2) lo hi rest
            true lead no_run fp first
        end else begin
          flush_agree h1 h2 lo hi cur.fb cur.rw fp;
          let (h1', fp') = flush_blue_x h1 cur.fb cur.rw fp in
          let (h2', _) = flush_blue_x h2 cur.fb cur.rw fp in
          let first' =
            match first with
            | Some _ -> first
            | None -> if fp' <> fp then Some fp' else None in
          makeWhite_agree h1' h2' lo hi obj;
          seg_aux_agree g01 g02 (makeWhite_x obj h1') (makeWhite_x obj h2') lo hi rest
            true lead no_run fp' first'
        end
      else begin
        let ws = U64.v (wosize_x obj g01) in
        if seen then seg_aux_agree g01 g02 h1 h2 lo hi rest seen lead (extend cur obj ws) fp first
        else seg_aux_agree g01 g02 h1 h2 lo hi rest seen (extend lead obj ws) cur fp first
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// The lemma
/// ---------------------------------------------------------------------------

let sweep_segment_local (g1 g2: heap) (lo: hp_addr) (hi: nat)
  : Lemma (requires U64.v lo <= hi /\ hi <= heap_size /\ hi % 8 == 0 /\
                    Seq.slice g1 (U64.v lo) hi == Seq.slice g2 (U64.v lo) hi)
          (ensures (let o1 = sweep_segment g1 lo hi in
                    let o2 = sweep_segment g2 lo hi in
                    Seq.slice o1.sheap (U64.v lo) hi == Seq.slice o2.sheap (U64.v lo) hi /\
                    o1.all_free == o2.all_free /\
                    o1.lead == o2.lead /\
                    o1.trail == o2.trail /\
                    o1.first_link == o2.first_link /\
                    o1.local_head == o2.local_head))
  = agree_of_slice g1 g2 (U64.v lo) hi;
    seg_objects_agree g1 g2 (U64.v lo) lo hi;
    seg_aux_agree g1 g2 g1 g2 (U64.v lo) hi (seg_objects g1 lo hi)
      false no_run no_run 0UL None;
    slice_of_agree (sweep_segment g1 lo hi).sheap (sweep_segment g2 lo hi).sheap (U64.v lo) hi

/// ---------------------------------------------------------------------------
/// Non-vacuity
/// ---------------------------------------------------------------------------

/// The hypothesis holds for heaps that differ: here, in a word below
/// zero_addr, outside the whole-heap segment [zero_addr, heap_size).  Every
/// lemma above is called, through this one, on arguments meeting its
/// precondition.
let local_witness (g: heap) (v: U64.t) : unit =
  let g2 = write_word g 0UL v in
  zero_addr_above_2048 ();
  write_word_spec g 0UL v;
  Seq.lemma_eq_intro (Seq.slice g (U64.v zero_addr) heap_size)
                     (Seq.slice g2 (U64.v zero_addr) heap_size);
  sweep_segment_local g g2 zero_addr heap_size
