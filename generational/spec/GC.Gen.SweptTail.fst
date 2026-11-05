module GC.Gen.SweptTail

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FusedSweep
open GC.Spec.FusedSweep.Inv
open GC.Spec.SweepPhase.Util
open GC.Spec.SweepPhase.Intrinsic
open GC.Spec.Phase
open GC.Gen.MinorHeap
open GC.Gen.AllocShape

module U64 = FStar.UInt64
module W = GC.Spec.Walk
module FL = GC.Spec.FreeList
module FLA = GC.Spec.FreeList.Ascending
module SA = GC.Spec.Allocator
module AC = GC.Spec.Allocator.Cursor
module AP = GC.Gen.AllocPhase
module Promote = GC.Gen.Promote
module WB = GC.Gen.WriteBodyLemmas
module PUO = GC.Gen.PromoteUpdate.Obj

#set-options "--fuel 0 --ifuel 1 --z3rlimit 10"

/// ---------------------------------------------------------------------------
/// The last cell below a point
/// ---------------------------------------------------------------------------

/// The spec pins `max_cell_below` down.
let max_cell_unique (g: heap) (x: nat) (m: U64.t)
  : Lemma (requires (m == 0UL \/ (FL.fl_cell g m /\ U64.v m <= x)) /\
                    (forall (y: U64.t). FL.fl_cell g y /\ U64.v y <= x ==> m <> 0UL /\ U64.v y <= U64.v m))
          (ensures max_cell_below g x == m)
  = max_cell_below_spec g x

/// ---------------------------------------------------------------------------
/// One allocation
/// ---------------------------------------------------------------------------

/// The found case of an allocation from `g`, by the block `cur` (with list
/// predecessor `p`) and its pieces.
let found_at (g: heap) (fp: U64.t) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece) : prop =
  FLA.fl_ascending g fp /\ FL.fl_cell g cur /\
  AC.fits_at g cur (AC.req_wz wz) /\ linked_to g fp p cur /\
  piece_ok g cur (AC.req_wz wz) pc /\
  SA.alloc_spec g fp wz tag == SA.alloc_search g fp p cur (AC.req_wz wz) SA.Idle tag 1 /\
  AC.alloc_choice g fp wz == (p, cur)

/// The allocation's found case, from the idle allocation's.
#push-options "--z3rlimit 20"
let alloc_found_at (g: heap) (fp: U64.t) (wz: nat) (tag: tag_t)
  : Ghost (U64.t & U64.t & piece)
      (requires FLA.fl_ascending g fp /\ snd (AC.alloc_choice g fp wz) <> 0UL)
      (ensures fun (p, cur, pc) ->
         found_at g fp wz tag p cur pc /\
         (let r = SA.alloc_spec g fp wz tag in
          let w = AC.req_wz wz in
          r.SA.heap_out == at_heap g p cur w tag pc heap_size_u64 /\
          r.SA.fp_out == spec_fp g fp p cur pc /\
          U64.v r.SA.obj_out == U64.v pc.ah + 8))
  = choice_facts g fp wz SA.Idle tag;
    AC.alloc_phase_idle g fp wz tag;
    let (p, cur) = AC.alloc_choice g fp wz in
    let w = AC.req_wz wz in
    let pc = mk_piece g cur w in
    spec_explicit g fp wz SA.Idle tag p cur pc;
    spec_heap_idle g fp p cur w tag pc;
    (p, cur, pc)
#pop-options

/// The last cell at or below `t0`, after the allocation.
let tail_step (g: heap) (fp: U64.t) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece) (t0: nat)
  : Lemma (requires found_at g fp wz tag p cur pc)
          (ensures (let gI = at_heap g p cur (AC.req_wz wz) tag pc heap_size_u64 in
                    let tn = max_cell_below g t0 in
                    max_cell_below gI t0 == (if cur = tn && pc.lo < 2 then p else tn) /\
                    (cur = tn && AC.takes_off g cur wz <==> cur = tn && pc.lo < 2)))
  = let w = AC.req_wz wz in
    let gI = at_heap g p cur w tag pc heap_size_u64 in
    let tn = max_cell_below g t0 in
    cell_facts g fp p cur w pc;
    at_cells g fp p cur w tag pc heap_size_u64;
    max_cell_below_spec g t0;
    let m = if cur = tn && pc.lo < 2 then p else tn in
    max_cell_unique gI t0 m

/// The fragment at `n` is read off the walk position `n - 8` and its header.
let frag_at_congr (g g': heap) (n: nat)
  : Lemma (requires (n >= 8 ==>
                      (W.reaches g' zero_addr (n - 8) <==> W.reaches g zero_addr (n - 8))) /\
                    (n >= 8 /\ n < heap_size /\ n % 8 = 0 /\ W.reaches g zero_addr (n - 8) ==>
                      getWosize (read_word g' (mk_hp_addr (n - 8))) ==
                        getWosize (read_word g (mk_hp_addr (n - 8))) /\
                      blue_at g' (mk_hp_addr (n - 8)) == blue_at g (mk_hp_addr (n - 8))))
          (ensures frag_at g' n == frag_at g n)
  = ()

/// A recolouring keeps the derived state.
let recoloured_state (g g': heap) (c: U64.t)
  : Lemma (requires AP.recoloured g g')
          (ensures state_at g' c == state_at g c /\
                   (W.reaches g' zero_addr (U64.v c) <==> W.reaches g zero_addr (U64.v c)))
  = AP.recoloured_facts g g';
    (if U64.v c > 0 then max_cell_below_congr g g' (U64.v c - 1));
    frag_at_congr g g' (U64.v c)

/// The fragment at the cursor, and the cursor, across the idle allocation's
/// writes: they are inside the cell's block, and the cursor is not.
let frag_step (g: heap) (fp: U64.t) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece) (c: U64.t)
  : Lemma (requires found_at g fp wz tag p cur pc /\ W.reaches g zero_addr (U64.v c))
          (ensures (let gI = at_heap g p cur (AC.req_wz wz) tag pc heap_size_u64 in
                    W.reaches gI zero_addr (U64.v c) /\ frag_at gI (U64.v c) == frag_at g (U64.v c)))
  = let w = AC.req_wz wz in
    let gI = at_heap g p cur w tag pc heap_size_u64 in
    let n = U64.v c in
    cell_facts g fp p cur w pc;
    at_shape g fp p cur w tag pc heap_size_u64;
    W.bnext_facts g pc.hd;
    (if U64.v pc.hd < n && n < pc.e then no_pos_inside g pc.hd n);
    if n >= 8 then begin
      let q = n - 8 in
      if U64.v pc.hd < q && q < pc.e then begin
        // the cursor ends the cell's block, and nothing of either walk ends
        // at it inside the block
        (if W.reaches g zero_addr q then no_pos_inside g pc.hd q);
        assert (~(W.reaches gI zero_addr q))
      end else if n >= U64.v zero_addr + 8 && n < heap_size && n % 8 = 0 then begin
        let qa = mk_hp_addr q in
        if p <> 0UL && U64.v p = q then assert (~(W.reaches g zero_addr q))
        else ()
      end
    end;
    frag_at_congr g gI n

/// The derived state after the allocation is the one before, with the
/// in-place update.
let alloc_caches g fp c wz tag =
  let n = U64.v c in
  let ph0 = Sweeping c in
  choice_facts g fp wz SA.Idle tag;
  AP.alloc_at_fields ph0 g fp wz tag;
  AC.alloc_phase_idle g fp wz tag;
  FLA.fl_ascending_valid g fp;
  part1_holds g;
  if snd (AC.alloc_choice g fp wz) = 0UL then
    choice_facts g fp wz ph0 tag
  else begin
    let (p, cur, pc) = alloc_found_at g fp wz tag in
    (if n > 0 then tail_step g fp wz tag p cur pc (n - 1));
    frag_step g fp wz tag p cur pc c;
    AP.alloc_at_recoloured ph0 g fp wz tag;
    let gI = (SA.alloc_spec g fp wz tag).SA.heap_out in
    let g' = (AP.alloc_at ph0 g fp wz tag).SA.heap_out in
    recoloured_state gI g' c
  end

/// ---------------------------------------------------------------------------
/// Copying keeps the walk and the headers
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20"
let rec copy_heads (g: heap) (minor: minor_state) (src: U64.t) (dst: obj_addr) (i n: nat)
  : Lemma (requires Seq.mem dst (objects zero_addr g) /\ ~(is_blue dst g) /\
                    n <= U64.v (wosize_of_object dst g))
          (ensures same_heads g (WB.copy_fields minor g src dst i n))
          (decreases (n - i))
  = if i >= n then WB.copy_fields_base minor g src dst i n
    else begin
      part1_holds g;
      wfh_part1_obj_bound g dst;
      hd_address_spec dst;
      obj_pos g dst; colour_of g dst;
      W.bnext_facts g (hd_address dst);
      let a : hp_addr = U64.uint_to_t (U64.v dst + i * 8) in
      let v = minor_read_field minor src i in
      let off (x: nat) : Lemma (W.reaches g zero_addr x ==> x <> U64.v a)
        = if W.reaches g zero_addr x && x = U64.v a then no_pos_inside g (hd_address dst) x in
      FStar.Classical.forall_intro off;
      WB.copy_fields_step minor g src dst i n;
      write_off_walk g a v;
      body_write g 0UL (hd_address dst) a v;
      let g1 = write_word g a v in
      colour_of g1 dst;
      obj_pos g1 dst;
      copy_heads g1 minor src dst (i + 1) n
    end
#pop-options

#push-options "--z3rlimit 20"
let promote_heads ph0 g fp minor obj wz =
  let tag = Promote.promoted_tag minor obj in
  let ar = AP.alloc_at ph0 g fp wz tag in
  FLA.fl_ascending_valid g fp;
  part1_holds g;
  if ar.SA.obj_out = 0UL then begin
    AP.alloc_at_fields ph0 g fp wz tag;
    Promote.promote_object_oom minor g obj fp wz ph0
  end
  else begin
    Promote.promote_object_success minor g obj fp wz ph0;
    AP.alloc_at_recoloured ph0 g fp wz tag;
    AP.alloc_at_obj_wosize ph0 g fp wz tag;
    let dst : obj_addr = ar.SA.obj_out in
    copy_heads ar.SA.heap_out minor obj dst 0 wz
  end
#pop-options

/// ---------------------------------------------------------------------------
/// The pointer update keeps the walk and every header
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20"
let uop_heads (major: heap) (obj: obj_addr) (fwd: Promote.forwarding_map) (i: nat)
  : Lemma (requires Seq.mem obj (objects zero_addr major))
          (ensures same_heads major
                     (Promote.update_object_pointers major obj (U64.v (wosize_of_object obj major)) fwd i))
  = let wz = U64.v (wosize_of_object obj major) in
    let major' = Promote.update_object_pointers major obj wz fwd i in
    part1_holds major;
    wfh_part1_obj_bound major obj;
    hd_address_spec obj;
    obj_pos major obj; colour_of major obj;
    W.bnext_facts major (hd_address obj);
    let bnd (j: nat) : Lemma (j < wz ==> U64.v obj + j * 8 + 8 <= heap_size /\ (U64.v obj + j * 8) % 8 == 0)
      = () in
    FStar.Classical.forall_intro bnd;
    let at (q: hp_addr)
      : Lemma (requires W.reaches major zero_addr (U64.v q))
              (ensures read_word major' q == read_word major q)
      = if U64.v q < U64.v obj then PUO.update_object_pointers_preserves_addr_below major obj wz fwd i q
        else if U64.v q >= U64.v obj + wz * 8 then PUO.update_object_pointers_preserves_addr_above major obj wz fwd i q
        else no_pos_inside major (hd_address obj) (U64.v q)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires at);
    W.walk_congr major major' zero_addr
#pop-options

#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
let rec uwa_heads (major: heap) (objs: seq obj_addr) (upd: obj_addr -> GTot bool)
                  (fwd: Promote.forwarding_map) (idx: nat)
  : Lemma (requires objs == objects zero_addr major)
          (ensures same_heads major (Promote.update_walk_aux major objs upd fwd idx))
          (decreases (Seq.length objs - idx))
  = if idx >= Seq.length objs then ()
    else begin
      let obj = Seq.index objs idx in
      if not (upd obj) then
        uwa_heads major objs upd fwd (idx + 1)
      else if is_no_scan obj major then uwa_heads major objs upd fwd (idx + 1)
      else begin
        let wz = U64.v (wosize_of_object obj major) in
        let major' = Promote.update_object_pointers major obj wz fwd 0 in
        uop_heads major obj fwd 0;
        same_heads_facts major major';
        uwa_heads major' objs upd fwd (idx + 1)
      end
    end
#pop-options

let update_heads major free fwd =
  uwa_heads major (objects zero_addr major) (in_use free major) fwd 0

