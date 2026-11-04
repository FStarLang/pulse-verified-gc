module GC.Gen.PaintUpdate

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FusedSweep.Inv
open GC.Spec.SweepPhase.Util
open GC.Spec.SweepPhase.Intrinsic
open GC.Gen.Base

module U64 = FStar.UInt64
module W = GC.Spec.Walk
module Promote = GC.Gen.Promote
module Paint = GC.Gen.Paint
module UP = GC.Gen.Impl.UpdatePtrs
module RT = GC.Gen.RefTable
module TPE = GC.Gen.TwoPassEquiv
module Ph = GC.Spec.Phase

#set-options "--fuel 0 --ifuel 1 --z3rlimit 10"

/// ---------------------------------------------------------------------------
/// One object
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20"
let rec uop_aux (c: nat) (g0 h: heap) (obj: obj_addr) (wz: nat) (fwd: Promote.forwarding_map) (i: nat)
  : Lemma (requires Seq.mem obj (objects zero_addr h) /\ wz == U64.v (wosize_of_object obj h))
          (ensures (let h' = Promote.update_object_pointers h obj wz fwd i in
                    same_heads h h' /\
                    Paint.paint c g0 h' == Promote.update_object_pointers (Paint.paint c g0 h) obj wz fwd i))
          (decreases (if i < wz then wz - i else 0))
  = let hp = Paint.paint c g0 h in
    if i >= wz then begin
      Promote.update_object_pointers_done h obj wz fwd i;
      Promote.update_object_pointers_done hp obj wz fwd i
    end else begin
      part1_holds h;
      wfh_part1_obj_bound h obj;
      hd_address_spec obj;
      obj_pos h obj; colour_of h obj;
      W.bnext_facts h (hd_address obj);
      let off : hp_addr = U64.uint_to_t (U64.v obj + i * 8) in
      Promote.update_object_pointers_step h obj wz fwd i;
      Promote.update_object_pointers_step hp obj wz fwd i;
      let not_pos (x: nat) : Lemma (W.reaches h zero_addr x ==> x <> U64.v off)
        = if W.reaches h zero_addr x && x = U64.v off then no_pos_inside h (hd_address obj) x in
      FStar.Classical.forall_intro not_pos;
      Paint.paint_read c g0 h off;
      let fv = to_minor_offset (read_word h off) in
      if Promote.is_minor_pointer fv && fwd fv <> 0UL then begin
        let v = fwd fv in
        let h1 = write_word h off v in
        write_off_walk h off v;
        Paint.paint_write c g0 h off v;
        same_heads_facts h h1;
        colour_of h1 obj;
        uop_aux c g0 h1 obj wz fwd (i + 1)
      end
      else uop_aux c g0 h obj wz fwd (i + 1)
    end
#pop-options

let paint_uop c g0 h obj fwd i =
  uop_aux c g0 h obj (U64.v (wosize_of_object obj h)) fwd i

/// ---------------------------------------------------------------------------
/// The first pass
/// ---------------------------------------------------------------------------

/// The update of one promoted object keeps the others valid.
#push-options "--z3rlimit 20"
let valid_after_uop (h: heap) (farr: seq U64.t) (fwd: Promote.forwarding_map) (idx: nat) (e: obj_addr)
  : Lemma (requires UP.promoted_entries_valid_from h farr idx /\ Seq.mem e (objects zero_addr h) /\
                    U64.v (wosize_of_object e h) > 0)
          (ensures (let h' = Promote.update_object_pointers h e (U64.v (wosize_of_object e h)) fwd 0 in
                    UP.promoted_entries_valid_from h' farr (idx + 1)))
  = let wz = U64.v (wosize_of_object e h) in
    let h' = Promote.update_object_pointers h e wz fwd 0 in
    paint_uop 0 h h e fwd 0;
    same_heads_facts h h';
    part1_holds h; part1_holds h';
    wfh_part1_obj_bound h e;
    let one (o: obj_addr)
      : Lemma (requires is_infix o h) (ensures is_infix o h')
      = TPE.update_obj_ptrs_preserves_is_infix h e wz fwd o
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires one);
    let sz (x: obj_addr)
      : Lemma (requires Seq.mem x (objects zero_addr h))
              (ensures wosize_of_object x h' == wosize_of_object x h)
      = colour_of h x; colour_of h' x
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires sz)
#pop-options

#push-options "--z3rlimit 30"
let rec upi_aux (c: nat) (g0 h: heap) (farr: seq U64.t) (fwd: Promote.forwarding_map) (idx: nat)
  : Lemma (requires UP.promoted_entries_valid_from h farr idx)
          (ensures same_heads h (UP.update_promoted_iter h farr fwd idx) /\
                   UP.update_promoted_iter (Paint.paint c g0 h) farr fwd idx ==
                   Paint.paint c g0 (UP.update_promoted_iter h farr fwd idx))
          (decreases (UP.fwd_array_size - idx))
  = let hp = Paint.paint c g0 h in
    if idx >= UP.fwd_array_size then begin
      UP.update_promoted_iter_done h farr fwd idx;
      UP.update_promoted_iter_done hp farr fwd idx
    end else begin
      let e = Seq.index farr idx in
      if e = 0UL then begin
        UP.update_promoted_iter_zero h farr fwd idx;
        UP.update_promoted_iter_zero hp farr fwd idx;
        upi_aux c g0 h farr fwd (idx + 1)
      end else begin
        let hdr_addr = U64.v e - 8 in
        if hdr_addr + 8 > heap_size || hdr_addr % 8 <> 0 || U64.v e < 8 then begin
          (if U64.v e < 8 then assert False);
          UP.update_promoted_iter_skip h farr fwd idx;
          UP.update_promoted_iter_skip hp farr fwd idx;
          upi_aux c g0 h farr fwd (idx + 1)
        end else begin
          let ha : hp_addr = U64.uint_to_t hdr_addr in
          Paint.paint_read c g0 h ha;
          black_header_facts (read_word h ha);
          let hdr = read_word h ha in
          let wz = U64.v (getWosize hdr) in
          let tag = getTag hdr in
          if wz > 0 && U64.lt tag no_scan_tag && tag <> infix_tag && U64.v e + wz * 8 <= heap_size
          then begin
            UP.update_promoted_iter_scan h farr fwd idx;
            UP.update_promoted_iter_scan hp farr fwd idx;
            let o : obj_addr = e in
            hd_address_spec o;
            is_infix_spec o h;
            tag_of_object_spec o h;
            wosize_of_object_spec o h;
            assert (~(is_infix o h));
            assert (Seq.mem o (objects zero_addr h));
            assert (U64.v (wosize_of_object o h) == wz);
            paint_uop c g0 h o fwd 0;
            valid_after_uop h farr fwd idx o;
            let h' = Promote.update_object_pointers h o wz fwd 0 in
            upi_aux c g0 h' farr fwd (idx + 1)
          end else begin
            UP.update_promoted_iter_skip h farr fwd idx;
            UP.update_promoted_iter_skip hp farr fwd idx;
            upi_aux c g0 h farr fwd (idx + 1)
          end
        end
      end
    end
#pop-options

let paint_upi c g0 h farr fwd idx = upi_aux c g0 h farr fwd idx

/// ---------------------------------------------------------------------------
/// The second pass
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20 --fuel 1"
let rec rsi_aux (c: nat) (g0 h: heap) (fwd: Promote.forwarding_map) (slots: seq U64.t) (n: nat) (idx: nat)
  : Lemma (requires slots_off_walk h slots n)
          (ensures same_heads h (UP.rewrite_slots_iter h fwd slots n idx) /\
                   UP.rewrite_slots_iter (Paint.paint c g0 h) fwd slots n idx ==
                   Paint.paint c g0 (UP.rewrite_slots_iter h fwd slots n idx))
          (decreases (n - idx))
  = if idx >= n || idx >= Seq.length slots then ()
    else begin
      let sa = Seq.index slots idx in
      if U64.v sa >= heap_size || U64.v sa % 8 <> 0 then rsi_aux c g0 h fwd slots n (idx + 1)
      else begin
        let a : hp_addr = sa in
        Paint.paint_read c g0 h a;
        let fv = to_minor_offset (read_word h a) in
        if Promote.is_minor_pointer fv && fwd fv <> 0UL then begin
          let v = fwd fv in
          let not_pos (x: nat) : Lemma (W.reaches h zero_addr x ==> x <> U64.v a) = () in
          FStar.Classical.forall_intro not_pos;
          write_off_walk h a v;
          Paint.paint_write c g0 h a v;
          let h1 = write_word h a v in
          rsi_aux c g0 h1 fwd slots n (idx + 1)
        end
        else rsi_aux c g0 h fwd slots n (idx + 1)
      end
    end
#pop-options

let paint_rsi c g0 h fwd slots n idx = rsi_aux c g0 h fwd slots n idx

#push-options "--z3rlimit 20"
let slots_off_walk_of_sound free s slots n h =
  assert (n <= Seq.length slots);
  let one (i: nat)
    : Lemma (requires i < n /\ n <= Seq.length slots)
            (ensures i < Seq.length slots /\ (let a = U64.v (Seq.index slots i) in
                      a < heap_size /\ a % 8 == 0 /\ ~(W.reaches h zero_addr a)))
    = let a = U64.v (Seq.index slots i) in
      eliminate exists (obj: obj_addr) (j: nat).
        in_use free s obj /\ is_no_scan obj s = false /\
        j < U64.v (wosize_of_object obj s) /\ a == U64.v obj + j * 8
      with begin
        in_use_not_blue free s obj;
        obj_pos s obj; colour_of s obj;
        hd_address_spec obj;
        let q = hd_address obj in
        assert (pos h q /\ read_word h q == read_word s q);
        W.bnext_facts h q;
        if W.reaches h zero_addr a then no_pos_inside h q a
      end
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires one)
#pop-options

#push-options "--z3rlimit 20"
let paint_two_pass ph g0 h farr fwd slots n =
  let c = match ph with | Ph.Idle -> 0 | Ph.Sweeping st -> U64.v st.GC.Spec.FusedSweep.cursor in
  paint_upi c g0 h farr fwd 0;
  let h1 = UP.update_promoted_iter h farr fwd 0 in
  same_heads_facts h h1;
  assert (slots_off_walk h1 slots n);
  paint_rsi c g0 h1 fwd slots n 0
#pop-options
