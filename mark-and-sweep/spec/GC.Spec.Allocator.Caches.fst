module GC.Spec.Allocator.Caches

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
open GC.Spec.Allocator.Shape

module U64 = FStar.UInt64
module W = GC.Spec.Walk
module FL = GC.Spec.FreeList
module FLA = GC.Spec.FreeList.Ascending
module SA = GC.Spec.Allocator
module AC = GC.Spec.Allocator.Cursor
module AP = GC.Spec.Allocator.Phase

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
      end else if n < heap_size && n % 8 = 0 && W.reaches g zero_addr q then begin
        // a position of the walk outside the block, and not the cell's own
        // header (the cursor would be inside the block), nor `p` (an object)
        W.reaches_bounds g zero_addr q;
        let qa = mk_hp_addr q in
        assert (q <> U64.v pc.hd);
        assert (p == 0UL \/ U64.v qa <> U64.v p);
        assert (read_word gI qa == read_word g qa)
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
