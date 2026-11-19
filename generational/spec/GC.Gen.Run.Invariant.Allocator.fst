/// ---------------------------------------------------------------------------
/// GC.Gen.Run.Invariant.Allocator - `alloc_phase` is a direct major allocation
/// ---------------------------------------------------------------------------
///
/// The proof of `GC.Gen.Run.Invariant.alloc_phase_major_alloc_step`: the
/// allocator (`AC.alloc_phase`, first fit at the phase) followed by the
/// initialising writes (`write_major_fields`) meets the relational step
/// `major_alloc_step`, properties (1)-(4).
///
/// The allocation is read at every phase through the sweep's form of it
/// (`GC.Spec.Allocator.Shape.at_heap`, the heap `alloc_spec` leaves with the
/// object's header black when it is at or in front of a cursor): idle is the
/// cursor past the heap (white), marking the cursor at 0 (black), mid-sweep
/// the sweep's own cursor (`cur_of`).  From it: the object is carved out of a
/// free cell of the list (1), with the requested header (2), and the words
/// it changes are the cell's header, the object's header and the
/// predecessor cell's link, so every other allocated block keeps its header
/// and fields (3).  The collector's state afterwards (4) is the phase's own
/// allocation lemmas: marking `GC.Gen.MarkPhase.Alloc` (fresh, then closed),
/// mid-sweep `GC.Spec.SweepPhase.Mutator` (fresh, then closed), idle the
/// pointer clauses closed here (`close_fresh`).

module GC.Gen.Run.Invariant.Allocator

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FusedSweep
open GC.Spec.FusedSweep.Inv
open GC.Spec.SweepPhase.Util
open GC.Gen.MinorHeap
open GC.Gen.Run.Step
open GC.Gen.Run.History

module U64 = FStar.UInt64
module Ph = GC.Spec.Phase
module MP = GC.Spec.MarkPhase
module MM = GC.Spec.MarkPhase.Mutator
module MPA = GC.Spec.MarkPhase.Alloc
module SA = GC.Spec.Allocator
module AC = GC.Spec.Allocator.Cursor
module ASh = GC.Spec.Allocator.Shape
module FL = GC.Spec.FreeList
module FLA = GC.Spec.FreeList.Ascending
module LL = GC.Spec.FusedSweep.Lossless
module W = GC.Spec.Walk
module SPI = GC.Spec.SweepPhase.Intrinsic
module SPM = GC.Spec.SweepPhase.Mutator
module GI = GC.Gen.Incremental
module GMA = GC.Gen.MarkPhase.Alloc
module GMM = GC.Gen.MarkPhase.Minor
module RT = GC.Gen.RefTable
module GenInv = GC.Gen.HeapInvariant
module PCS = GC.Gen.PostCollectionShape
module Promote = GC.Gen.Promote
module Mark = GC.Spec.Mark
module Header = GC.Lib.Header
module SweepInv = GC.Spec.SweepInv
module PD = GC.Gen.Run.Invariant.ProgramDefs
module I = GC.Model.Ideal

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The initialising writes
/// ---------------------------------------------------------------------------

/// The `j`-th field slot of `a`.
let slot (a: obj_addr) (j: nat) : nat = U64.v a + 8 * j

/// The writes fit: every field slot of `a` is in the heap.
let fits (a: obj_addr) (init: seq U64.t) : prop =
  U64.v a + 8 * Seq.length init <= heap_size

/// Every word after the writes from field `i` on: the initial value at a
/// slot written, the word before elsewhere.
#push-options "--fuel 1 --z3rlimit 40"
let rec wmf_read (g: heap) (a: obj_addr) (init: seq U64.t) (i: nat) (q: hp_addr)
  : Lemma (requires fits a init)
          (ensures read_word (PD.write_major_fields g a init i) q ==
                   (if U64.v q >= slot a i && U64.v q < U64.v a + 8 * Seq.length init
                    then Seq.index init ((U64.v q - U64.v a) / 8)
                    else read_word g q))
          (decreases (Seq.length init - i))
  = if i >= Seq.length init then ()
    else begin
      let p = U64.v a + 8 * i in
      assert (p + 8 <= heap_size /\ p % 8 = 0);
      let pa : hp_addr = U64.uint_to_t p in
      let g1 = write_word g pa (Seq.index init i) in
      wmf_read g1 a init (i + 1) q;
      if U64.v q = p then read_write_same g pa (Seq.index init i)
      else read_write_different g pa q (Seq.index init i)
    end
#pop-options

/// The field `j` of `a` after all the writes.
let wmf_field (g: heap) (a: obj_addr) (init: seq U64.t) (j: nat)
  : Lemma (requires fits a init /\ j < Seq.length init)
          (ensures major_field (PD.write_major_fields g a init 0) a j == Seq.index init j)
  = let p = U64.v a + j * 8 in
    assert (p + 8 <= heap_size /\ p % 8 = 0);
    wmf_read g a init 0 (U64.uint_to_t p);
    assert ((p - U64.v a) / 8 == j)

/// A property kept by every write into the body of `a` is kept by the
/// initialising writes.
#push-options "--fuel 1 --z3rlimit 40"
let rec wmf_ind (pr: heap -> prop) (a: obj_addr) (init: seq U64.t) (i: nat) (g: heap)
    (step: (h: heap) -> (q: hp_addr) -> (v: U64.t) ->
           Lemma (requires pr h /\ SPM.in_body h a q) (ensures pr (write_word h q v)))
    (size_kept: (h: heap) -> Lemma (requires pr h) (ensures U64.v (wosize_of_object a h) == Seq.length init))
  : Lemma (requires pr g /\ fits a init)
          (ensures pr (PD.write_major_fields g a init i))
          (decreases (Seq.length init - i))
  = if i >= Seq.length init then ()
    else begin
      let p = U64.v a + 8 * i in
      assert (p + 8 <= heap_size /\ p % 8 = 0);
      let pa : hp_addr = U64.uint_to_t p in
      size_kept g;
      step g pa (Seq.index init i);
      wmf_ind pr a init (i + 1) (write_word g pa (Seq.index init i)) step size_kept
    end
#pop-options

/// ---------------------------------------------------------------------------
/// The allocation at any phase, as the sweep's allocation at a cursor
/// ---------------------------------------------------------------------------

/// The cursor whose allocation colour is the phase's everywhere: past the
/// heap when idle (white), 0 while marking (black), the sweep's own.
let cur_of (ph: Ph.gc_phase) : U64.t =
  match ph with
  | Ph.Idle -> heap_size_u64
  | Ph.Marking -> 0UL
  | Ph.Sweeping c -> c

let colour_cur (ph: Ph.gc_phase) (hd: hp_addr)
  : Lemma (Ph.allocation_color ph hd == Ph.allocation_color (Ph.Sweeping (cur_of ph)) hd)
  = ()

/// The allocation at `ph` is the allocation at `Sweeping (cur_of ph)`.
let same_alloc (g: heap) (fp: U64.t) (ph: Ph.gc_phase) (wz: nat) (tag: SPM.tag_t)
  : Lemma (let r = AC.alloc_phase g fp ph wz tag in
           let rs = AC.alloc_phase g fp (Ph.Sweeping (cur_of ph)) wz tag in
           r.SA.heap_out == rs.SA.heap_out /\ r.SA.fp_out == rs.SA.fp_out /\ r.SA.obj_out == rs.SA.obj_out)
  = let ps = Ph.Sweeping (cur_of ph) in
    AC.alloc_phase_fields g fp ph wz tag;
    AC.alloc_phase_fields g fp ps wz tag;
    AC.alloc_phase_heap g fp ph wz tag;
    AC.alloc_phase_heap g fp ps wz tag;
    let r = AC.alloc_phase g fp ph wz tag in
    if r.SA.obj_out <> 0UL then colour_cur ph (hd_address (r.SA.obj_out <: obj_addr))

/// What the allocation found: the predecessor, the cell, its pieces.
let found_ok (g: heap) (fp: U64.t) (ph: Ph.gc_phase) (wz: nat) (tag: SPM.tag_t)
             (p cur: U64.t) (pc: ASh.piece) : prop =
  let w = AC.req_wz wz in
  let r = AC.alloc_phase g fp ph wz tag in
  FLA.fl_ascending g fp /\ FL.fl_cell g cur /\ AC.fits_at g cur w /\ ASh.linked_to g fp p cur /\
  ASh.piece_ok g cur w pc /\
  SA.alloc_spec g fp wz tag == SA.alloc_search g fp p cur w SA.Idle tag 1 /\
  r.SA.heap_out == ASh.at_heap g p cur w tag pc (cur_of ph) /\
  r.SA.fp_out == ASh.spec_fp g fp p cur pc /\
  U64.v r.SA.obj_out == U64.v pc.ASh.ah + 8 /\ is_obj r.SA.obj_out /\
  hd_address (r.SA.obj_out <: obj_addr) == pc.ASh.ah

#push-options "--z3rlimit 30"
let found (g: heap) (fp: U64.t) (ph: Ph.gc_phase) (wz: nat) (tag: SPM.tag_t)
  : Ghost (U64.t & U64.t & ASh.piece)
      (requires FLA.fl_ascending g fp /\ (AC.alloc_phase g fp ph wz tag).SA.obj_out <> 0UL)
      (ensures fun (p, cur, pc) -> found_ok g fp ph wz tag p cur pc)
  = let c = cur_of ph in
    let ps = Ph.Sweeping c in
    same_alloc g fp ph wz tag;
    ASh.choice_facts g fp wz ps tag;
    ASh.choice_facts g fp wz Ph.Idle tag;
    AC.alloc_phase_idle g fp wz tag;
    let (p, cur) = AC.alloc_choice g fp wz in
    let w = AC.req_wz wz in
    let pc = ASh.mk_piece g cur w in
    ASh.at_explicit g fp wz tag c p cur pc;
    (p, cur, pc)
#pop-options

/// ---------------------------------------------------------------------------
/// The blocks of the heap the allocation leaves
/// ---------------------------------------------------------------------------

/// Two blocks of a walk do not overlap: a word strictly inside one is not
/// strictly inside another, nor its header.
#push-options "--z3rlimit 30"
let disjoint_blocks (g: heap) (q1 q2: hp_addr) (b: nat)
  : Lemma (requires W.reaches g zero_addr (U64.v q1) /\ W.reaches g zero_addr (U64.v q2) /\ q1 <> q2 /\
                    U64.v q1 < b /\ b < W.bnext g q1)
          (ensures ~(U64.v q2 <= b /\ b < W.bnext g q2))
  = if U64.v q2 <= b && b < W.bnext g q2 then begin
      if U64.v q1 < U64.v q2 then no_pos_inside g q1 (U64.v q2)
      else no_pos_inside g q2 (U64.v q1)
    end
#pop-options

/// A cell's link word is in no other block of the walk.
#push-options "--z3rlimit 20"
let link_outside (g: heap) (hx: hp_addr) (p: U64.t) (q: hp_addr)
  : Lemma (requires W.reaches g zero_addr (U64.v hx) /\ not (blue_at g hx) /\ FL.fl_cell g p /\
                    U64.v hx < U64.v q /\ U64.v q < W.bnext g hx /\ U64.v q == U64.v p)
          (ensures False)
  = fl_cell_iff g p;
    wosize_at_hd g p;
    let hp = mk_hp_addr (U64.v p - 8) in
    assert (W.reaches g zero_addr (U64.v hp) /\ W.can_step g hp /\ blue_at g hp);
    assert (W.bnext g hp > U64.v p);
    disjoint_blocks g hx hp (U64.v q)
#pop-options

/// A block of the walk other than the cell lies outside the cell's block.
#push-options "--z3rlimit 20"
let outside_cell (g: heap) (hx hd: hp_addr) (e: nat) (q: nat)
  : Lemma (requires W.reaches g zero_addr (U64.v hx) /\ W.reaches g zero_addr (U64.v hd) /\
                    W.bnext g hd == e /\ hx <> hd /\ U64.v hx <= q /\ q < W.bnext g hx)
          (ensures (U64.v hx < U64.v hd \/ U64.v hx >= e) /\ (q < U64.v hd \/ q >= e))
  = (if U64.v hd < U64.v hx && U64.v hx < e then no_pos_inside g hd (U64.v hx));
    (if U64.v hx < U64.v hd && U64.v hd < W.bnext g hx then no_pos_inside g hx (U64.v hd))
#pop-options

/// Every block not free before keeps its header and body.
#push-options "--z3rlimit 40"
let kept_block (g: heap) (fp: U64.t) (ph: Ph.gc_phase) (wz: nat) (tag: SPM.tag_t)
               (p cur: U64.t) (pc: ASh.piece) (x: obj_addr)
  : Lemma (requires found_ok g fp ph wz tag p cur pc /\ Seq.mem x (objects zero_addr g) /\ ~(is_blue x g))
          (ensures (let gx = (AC.alloc_phase g fp ph wz tag).SA.heap_out in
                    Seq.mem x (objects zero_addr gx) /\
                    read_word gx (hd_address x) == read_word g (hd_address x) /\
                    hd_address x <> pc.ASh.ah /\ U64.v x <> U64.v pc.ASh.ah + 8 /\
                    (U64.v (hd_address x) < U64.v pc.ASh.hd \/ U64.v (hd_address x) >= pc.ASh.e) /\
                    (forall (q: hp_addr). U64.v (hd_address x) < U64.v q /\ U64.v q < W.bnext g (hd_address x) ==>
                       read_word gx q == read_word g q)))
  = let w = AC.req_wz wz in
    let c = cur_of ph in
    ASh.cell_facts g fp p cur w pc;
    let hx = hd_address x in
    SPI.obj_pos g x; SPI.colour_of g x;
    outside_cell g hx pc.ASh.hd pc.ASh.e (U64.v hx);
    (if p <> 0UL && U64.v hx = U64.v p then assert False);
    ASh.at_reach g fp p cur w tag pc c (U64.v hx);
    ASh.at_heap_read g fp p cur w tag pc c hx;
    SPI.obj_pos (ASh.at_heap g p cur w tag pc c) x;
    let body (q: hp_addr)
      : Lemma (requires U64.v hx < U64.v q /\ U64.v q < W.bnext g hx)
              (ensures read_word (ASh.at_heap g p cur w tag pc c) q == read_word g q)
      = outside_cell g hx pc.ASh.hd pc.ASh.e (U64.v q);
        (if p <> 0UL && U64.v q = U64.v p then link_outside g hx p q);
        ASh.at_heap_read g fp p cur w tag pc c q
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires body);
    hd_address_spec x
#pop-options

/// A block not free after, other than the new object, was one before, with
/// the same header.
#push-options "--z3rlimit 40"
let back_block (g: heap) (fp: U64.t) (ph: Ph.gc_phase) (wz: nat) (tag: SPM.tag_t)
               (p cur: U64.t) (pc: ASh.piece) (x: obj_addr)
  : Lemma (requires found_ok g fp ph wz tag p cur pc /\
                    Seq.mem x (objects zero_addr (AC.alloc_phase g fp ph wz tag).SA.heap_out) /\
                    ~(is_blue x (AC.alloc_phase g fp ph wz tag).SA.heap_out) /\
                    hd_address x <> pc.ASh.ah)
          (ensures Seq.mem x (objects zero_addr g) /\
                   read_word (AC.alloc_phase g fp ph wz tag).SA.heap_out (hd_address x) == read_word g (hd_address x))
  = let w = AC.req_wz wz in
    let c = cur_of ph in
    let gx = ASh.at_heap g p cur w tag pc c in
    ASh.cell_facts g fp p cur w pc;
    let hx = hd_address x in
    SPI.obj_pos gx x; SPI.colour_of gx x;
    hd_address_spec x;
    (if pc.ASh.lo = 0 then assert (U64.v pc.ASh.ah == U64.v pc.ASh.hd));
    if U64.v pc.ASh.hd < U64.v hx && U64.v hx < pc.ASh.e then begin
      ASh.at_shape g fp p cur w tag pc c;
      assert False
    end else if hx = pc.ASh.hd then begin
      ASh.at_heap_read g fp p cur w tag pc c hx;
      ASh.header_facts w tag pc.ASh.lo;
      assert False
    end else begin
      ASh.at_reach g fp p cur w tag pc c (U64.v hx);
      (if p <> 0UL then ASh.at_reach g fp p cur w tag pc c (U64.v p));
      assert (p <> 0UL ==> U64.v hx <> U64.v p);
      ASh.at_heap_read g fp p cur w tag pc c hx
    end;
    SPI.obj_pos g x
#pop-options

/// The new object: a block of the heap after, at the cell's end, with the
/// requested header; the cell was a free block of the heap before.
#push-options "--z3rlimit 40"
let new_block (g: heap) (fp: U64.t) (ph: Ph.gc_phase) (wz: nat) (tag: SPM.tag_t)
              (p cur: U64.t) (pc: ASh.piece)
  : Lemma (requires found_ok g fp ph wz tag p cur pc /\ wz >= 1)
          (ensures (let r = AC.alloc_phase g fp ph wz tag in
                    let gx = r.SA.heap_out in
                    let a : obj_addr = r.SA.obj_out in
                    let ocur : obj_addr = cur in
                    Seq.mem a (objects zero_addr gx) /\ ~(is_blue a gx) /\
                    U64.v (wosize_of_object a gx) == wz /\ tag_of_object a gx == tag /\
                    color_of_object a gx == Ph.allocation_color ph (hd_address a) /\
                    pos gx pc.ASh.ah /\ not (blue_at gx pc.ASh.ah) /\ W.bnext gx pc.ASh.ah == pc.ASh.e /\
                    U64.v a + 8 * wz == pc.ASh.e /\ pc.ASh.e <= heap_size /\
                    ~(Seq.mem a (objects zero_addr g) /\ ~(is_blue a g)) /\
                    Seq.mem ocur (objects zero_addr g) /\ is_blue ocur g /\
                    U64.v (hd_address ocur) <= U64.v pc.ASh.ah /\ LL.next_pos g ocur == pc.ASh.e))
  = let w = AC.req_wz wz in
    let c = cur_of ph in
    let r = AC.alloc_phase g fp ph wz tag in
    let gx = r.SA.heap_out in
    let a : obj_addr = r.SA.obj_out in
    ASh.cell_facts g fp p cur w pc;
    ASh.at_new_blocks g fp p cur w tag pc c;
    SPI.obj_pos gx a; SPI.colour_of gx a;
    hd_address_spec a;
    // the colour
    let front = U64.v pc.ASh.ah >= U64.v c in
    color_of_object_spec a gx;
    colour_cur ph pc.ASh.ah;
    ASh.header_facts w tag 1;
    assert (read_word gx pc.ASh.ah == ASh.object_header w tag front);
    assert (getColor (read_word gx pc.ASh.ah) == (if front then Header.Black else Header.White));
    // the cell
    let ocur : obj_addr = cur in
    fl_cell_iff g cur;
    SPI.obj_pos g ocur; SPI.colour_of g ocur;
    hd_address_spec ocur;
    // the new object was not a block in use before
    SPI.obj_pos g a; SPI.colour_of g a;
    if U64.v pc.ASh.hd < U64.v pc.ASh.ah && Seq.mem a (objects zero_addr g) then
      no_pos_inside g pc.ASh.hd (U64.v pc.ASh.ah)
#pop-options

/// ---------------------------------------------------------------------------
/// The initialising writes keep the walk and the headers
/// ---------------------------------------------------------------------------

let heads_from (gx: heap) (fp: U64.t) (ah: hp_addr) (h: heap) : prop =
  SPI.same_heads gx h /\ (FLA.fl_ascending gx fp ==> FLA.fl_ascending h fp)

#push-options "--z3rlimit 30"
let heads_step (gx: heap) (fp: U64.t) (a: obj_addr) (h: heap) (q: hp_addr) (v: U64.t)
  : Lemma (requires pos gx (hd_address a) /\ not (blue_at gx (hd_address a)) /\
                    heads_from gx fp (hd_address a) h /\ SPM.in_body h a q)
          (ensures heads_from gx fp (hd_address a) (write_word h q v))
  = let ah = hd_address a in
    hd_address_spec a;
    SPI.colour_of h a;
    assert (read_word h ah == read_word gx ah);
    assert (pos h ah);
    SPI.body_write h fp ah q v;
    SPM.same_heads_trans gx h (write_word h q v)
#pop-options

let after_writes (gx: heap) (fp: U64.t) (a: obj_addr) (init: seq U64.t)
  : Lemma (requires pos gx (hd_address a) /\ not (blue_at gx (hd_address a)) /\ fits a init /\
                    U64.v (wosize_of_object a gx) == Seq.length init)
          (ensures heads_from gx fp (hd_address a) (PD.write_major_fields gx a init 0))
  = let ah = hd_address a in
    SPM.same_heads_refl gx;
    let size_kept (h: heap) : Lemma (requires heads_from gx fp ah h)
                                    (ensures U64.v (wosize_of_object a h) == Seq.length init)
      = SPI.colour_of h a; SPI.colour_of gx a
    in
    wmf_ind (heads_from gx fp ah) a init 0 gx
      (fun h q v -> heads_step gx fp a h q v) size_kept

/// ---------------------------------------------------------------------------
/// Properties (1)-(3)
/// ---------------------------------------------------------------------------

/// What `major_alloc_step` asks of the new block `a` and the other blocks.
let block_facts (r: real_state) (tag: I.tag_t) (size: nat) (init: seq U64.t) (r': real_state) (a: obj_addr) : prop =
  Seq.length init == size /\
  was_free r.memory.major r'.memory.major a /\
  is_allocated r'.memory (Major a) /\
  tag_of_object a r'.memory.major == tag /\ U64.v (wosize_of_object a r'.memory.major) == size /\
  color_of_object a r'.memory.major == Ph.allocation_color r.phase (hd_address a) /\
  (forall (i: nat). i < size ==> block_field r'.memory (Major a) i == Seq.index init i) /\
  (forall (x: obj_addr). x <> a ==>
     (is_allocated r.memory (Major x) <==> is_allocated r'.memory (Major x)) /\
     (is_allocated r.memory (Major x) ==> same_block r.memory.major r'.memory.major x)) /\
  r'.ref_table == Seq.append r.ref_table (young_slots a init)

/// The setting: the heap before, the allocation's, the heap after the writes.
let setting (r: real_state) (tag: I.tag_t) (size: nat) (init: seq U64.t) : prop =
  FLA.fl_ascending r.memory.major r.free_list /\ size >= 1 /\ Seq.length init == size /\
  (AC.alloc_phase r.memory.major r.free_list r.phase size tag).SA.obj_out <> 0UL

/// An allocated block other than the new one keeps its header and fields.
#push-options "--z3rlimit 40"
let other_kept (g: heap) (fp: U64.t) (ph: Ph.gc_phase) (wz: nat) (tag: SPM.tag_t) (init: seq U64.t)
               (p cur: U64.t) (pc: ASh.piece) (x: obj_addr)
  : Lemma (requires found_ok g fp ph wz tag p cur pc /\ wz >= 1 /\ Seq.length init == wz /\
                    Seq.mem x (objects zero_addr g) /\ ~(is_blue x g))
          (ensures (let r = AC.alloc_phase g fp ph wz tag in
                    let g' = PD.write_major_fields r.SA.heap_out (r.SA.obj_out <: obj_addr) init 0 in
                    x <> (r.SA.obj_out <: obj_addr) /\
                    Seq.mem x (objects zero_addr g') /\ ~(is_blue x g') /\
                    same_block g g' x))
  = let r = AC.alloc_phase g fp ph wz tag in
    let gx = r.SA.heap_out in
    let a : obj_addr = r.SA.obj_out in
    let g' = PD.write_major_fields gx a init 0 in
    new_block g fp ph wz tag p cur pc;
    kept_block g fp ph wz tag p cur pc x;
    hd_address_spec a; hd_address_spec x;
    after_writes gx fp a init;
    SPI.same_heads_facts gx g';
    SPI.colour_of g x; SPI.colour_of gx x; SPI.colour_of g' x;
    SPI.obj_pos gx x;
    let hx = hd_address x in
    let field (i: nat)
      : Lemma (requires i < U64.v (wosize_of_object x g))
              (ensures major_field g' x i == major_field g x i)
      = let q = U64.v x + i * 8 in
        if q + 8 <= heap_size then begin
          let qa : hp_addr = U64.uint_to_t q in
          assert (U64.v hx < q /\ q < W.bnext g hx);
          disjoint_blocks gx hx pc.ASh.ah q;
          wmf_read gx a init 0 qa
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires field)
#pop-options

/// A block allocated after, other than the new one, was allocated before.
#push-options "--z3rlimit 40"
let other_back (g: heap) (fp: U64.t) (ph: Ph.gc_phase) (wz: nat) (tag: SPM.tag_t) (init: seq U64.t)
               (p cur: U64.t) (pc: ASh.piece) (x: obj_addr)
  : Lemma (requires found_ok g fp ph wz tag p cur pc /\ wz >= 1 /\ Seq.length init == wz /\
                    (let r = AC.alloc_phase g fp ph wz tag in
                     let g' = PD.write_major_fields r.SA.heap_out (r.SA.obj_out <: obj_addr) init 0 in
                     x <> (r.SA.obj_out <: obj_addr) /\
                     Seq.mem x (objects zero_addr g') /\ ~(is_blue x g')))
          (ensures Seq.mem x (objects zero_addr g) /\ ~(is_blue x g))
  = let r = AC.alloc_phase g fp ph wz tag in
    let gx = r.SA.heap_out in
    let a : obj_addr = r.SA.obj_out in
    let g' = PD.write_major_fields gx a init 0 in
    new_block g fp ph wz tag p cur pc;
    hd_address_spec a; hd_address_spec x;
    after_writes gx fp a init;
    SPI.same_heads_facts gx g';
    SPI.colour_of gx x; SPI.colour_of g' x;
    back_block g fp ph wz tag p cur pc x;
    SPI.colour_of g x
#pop-options

/// Properties (1)-(3), and the remembered set.
#push-options "--z3rlimit 40"
let alloc_block_facts (r: real_state) (tag: I.tag_t) (size: nat) (init: seq U64.t)
  : Lemma (requires setting r tag size init)
          (ensures is_obj (AC.alloc_phase r.memory.major r.free_list r.phase size tag).SA.obj_out /\
                   (let r' = PD.alloc_then_init r tag size init in
                    let a : obj_addr = (AC.alloc_phase r.memory.major r.free_list r.phase size tag).SA.obj_out in
                    block_facts r tag size init r' a))
  = let g = r.memory.major in
    let fp = r.free_list in
    let ph = r.phase in
    let res = AC.alloc_phase g fp ph size tag in
    let (p, cur, pc) = found g fp ph size tag in
    let gx = res.SA.heap_out in
    let a : obj_addr = res.SA.obj_out in
    let r' = PD.alloc_then_init r tag size init in
    let g' = r'.memory.major in
    assert (g' == PD.write_major_fields gx a init 0);
    new_block g fp ph size tag p cur pc;
    hd_address_spec a;
    after_writes gx fp a init;
    SPI.same_heads_facts gx g';
    SPI.colour_of gx a; SPI.colour_of g' a;
    color_of_object_spec a gx; color_of_object_spec a g';
    // (1)
    let ocur : obj_addr = cur in
    let fr (q: nat) : Lemma (requires LL.in_extent g' a q) (ensures LL.blue_covered g q)
      = assert (LL.in_extent g ocur q) in
    FStar.Classical.forall_intro (FStar.Classical.move_requires fr);
    // (2) the fields
    let fld (i: nat) : Lemma (i < Seq.length init ==> block_field r'.memory (Major a) i == Seq.index init i)
      = if i < Seq.length init then wmf_field gx a init i in
    FStar.Classical.forall_intro fld;
    // (3)
    let oth (x: obj_addr)
      : Lemma (requires x <> a)
              (ensures (is_allocated r.memory (Major x) <==> is_allocated r'.memory (Major x)) /\
                       (is_allocated r.memory (Major x) ==> same_block g g' x))
      = (if FStar.IndefiniteDescription.strong_excluded_middle (Seq.mem x (objects zero_addr g) /\ ~(is_blue x g))
         then other_kept g fp ph size tag init p cur pc x);
        if FStar.IndefiniteDescription.strong_excluded_middle (Seq.mem x (objects zero_addr g') /\ ~(is_blue x g'))
        then other_back g fp ph size tag init p cur pc x
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires oth)
#pop-options
