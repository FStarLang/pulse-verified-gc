module GC.Gen.Barrier

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.MinorHeap

module U64 = FStar.UInt64
module Ph = GC.Spec.Phase
module GenInv = GC.Gen.HeapInvariant
module GI = GC.Gen.Incremental
module GMM = GC.Gen.MarkPhase.Minor
module MM = GC.Spec.MarkPhase.Mutator
module MP = GC.Spec.MarkPhase
module SPM = GC.Spec.SweepPhase.Mutator
module SPI = GC.Spec.SweepPhase.Intrinsic
module SPU = GC.Spec.SweepPhase.Util
module RT = GC.Gen.RefTable
module Promote = GC.Gen.Promote
module GB = GC.Gen.Base
module W = GC.Spec.Walk
module FL = GC.Spec.FreeList
module FLA = GC.Spec.FreeList.Ascending
module PCS = GC.Gen.PostCollectionShape
module SweepInv = GC.Spec.SweepInv
module Mark = GC.Spec.Mark
module Header = GC.Lib.Header
module HeapGraph = GC.Spec.HeapGraph
module MS = GC.Gen.MarkState

#set-options "--fuel 0 --ifuel 1 --z3rlimit 10"

/// ---------------------------------------------------------------------------
/// The walk facts of each phase's shape
/// ---------------------------------------------------------------------------

/// What every phase's shape says of the walk and the list.
let walk_ok (g: heap) (fp: U64.t) : prop =
  heap_objects_dense g /\ Seq.length (objects zero_addr g) > 0 /\ FLA.fl_ascending g fp

#push-options "--z3rlimit 20"
let shape_facts (ph: Ph.gc_phase) (minor: minor_state) (g: heap) (fp: U64.t)
  : Lemma (requires GI.phase_shape minor g fp ph)
          (ensures free_def_ok (GI.phase_free ph) /\ well_formed_heap_with (GI.phase_free ph) g /\
                   walk_ok g fp /\ GenInv.minor_heap_shape minor /\
                   GenInv.minor_major_fields_not_free (GI.phase_free ph) minor g)
  = match ph with
    | Ph.Idle ->
        GI.phase_shape_idle minor g fp;
        GI.phase_free_idle ();
        free_stw_ok ();
        GenInv.collection_heap_shape_elim minor g fp;
        GenInv.major_heap_shape_elim g fp;
        GenInv.minor_major_fields_not_free_stw minor g
    | Ph.Marking ->
        GI.phase_shape_marking minor g fp;
        GI.phase_free_marking ();
        GenInv.collection_shape_with_elim Ph.Marking free_stw minor g fp;
        GenInv.major_shape_with_elim Ph.Marking free_stw g fp
    | Ph.Sweeping c ->
        GI.phase_shape_sweeping minor g fp c;
        GI.phase_free_sweeping c;
        SPI.free_incremental_ok c;
        SPI.sweep_inv_incremental_iff g fp c;
        SPI.sweep_shape_elim g fp c
#pop-options

/// ---------------------------------------------------------------------------
/// A write into a body
/// ---------------------------------------------------------------------------

/// The walk is a function of the positions: the same positions, the same
/// density.
let dense_transport (g g': heap)
  : Lemma (requires heap_objects_dense g /\ Seq.length (objects zero_addr g) > 0 /\ SPI.same_heads g g')
          (ensures heap_objects_dense g' /\ Seq.length (objects zero_addr g') > 0)
  = SPI.same_heads_facts g g';
    W.reaches_end_of_dense g;
    W.reaches_refl g zero_addr;
    W.dense_of_reaches_end g' (W.walk_end g zero_addr)

/// A write into the body of a block that is not free keeps the walk, every
/// header, the list and the non-free blocks.
#push-options "--z3rlimit 20"
let body_write_facts (g: heap) (fp: U64.t) (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) /\ SPM.in_body g x a /\ walk_ok g fp)
          (ensures (let g' = write_word g a v in
                    SPI.same_heads g g' /\ walk_ok g' fp /\
                    objects zero_addr g' == objects zero_addr g /\
                    (forall (y: obj_addr). Seq.mem y (objects zero_addr g) ==>
                       read_word g' (hd_address y) == read_word g (hd_address y)) /\
                    (forall (y: obj_addr) (free: free_def). free_def_ok free ==>
                       in_use free g' y == in_use free g y)))
  = let g' = write_word g a v in
    SPM.in_body_block g x a;
    SPI.colour_of g x;
    SPI.body_write g fp (hd_address x) a v;
    SPI.same_heads_facts g g';
    dense_transport g g'
#pop-options

/// The cross-generation condition depends only on the non-free blocks.
let mmf_transport (free: free_def) (minor: minor_state) (g g': heap)
  : Lemma (requires GenInv.minor_major_fields_not_free free minor g /\
                    (forall (y: obj_addr). in_use free g' y == in_use free g y))
          (ensures GenInv.minor_major_fields_not_free free minor g')
  = GenInv.minor_major_fields_not_free_intro free minor g'
      (fun obj j -> GenInv.minor_major_fields_not_free_elim free minor g obj j)

/// ---------------------------------------------------------------------------
/// Darkening
/// ---------------------------------------------------------------------------

/// A word in the body of a non-free block is no header.
let body_not_header (g: heap) (y t: obj_addr) (b: hp_addr)
  : Lemma (requires Seq.mem y (objects zero_addr g) /\ ~(is_blue y g) /\ SPM.in_body g y b /\
                    Seq.mem t (objects zero_addr g))
          (ensures hd_address t <> b)
  = SPM.in_body_block g y b;
    SPI.colour_of g y;
    SPI.body_word g (hd_address y) b;
    SPI.obj_pos g t

/// What greying the white block `t` keeps: everything but `t`'s colour.
#push-options "--z3rlimit 30"
let grey_facts (g: heap) (fp: U64.t) (t: obj_addr)
  : Lemma (requires Seq.mem t (objects zero_addr g) /\ is_white t g /\ walk_ok g fp)
          (ensures (let g1 = makeGray t g in
                    walk_ok g1 fp /\
                    objects zero_addr g1 == objects zero_addr g /\
                    (forall (y: obj_addr). in_use free_stw g1 y == in_use free_stw g y) /\
                    (forall (y: obj_addr).
                       is_no_scan y g1 == is_no_scan y g /\ is_closure y g1 == is_closure y g /\
                       wosize_of_object y g1 == wosize_of_object y g) /\
                    (forall (b: hp_addr). hd_address t <> b ==> read_word g1 b == read_word g b)))
  = let g1 = makeGray t g in
    makeGray_eq t g;
    makeGray_is_gray t g;
    color_change_preserves_objects g t Header.Gray;
    SweepInv.color_change_preserves_density t g Header.Gray;
    Mark.colors_exclusive t g;
    Mark.colors_exclusive t g1;
    let col (y: obj_addr)
      : Lemma ((is_blue y g1 <==> is_blue y g) /\
               is_no_scan y g1 == is_no_scan y g /\ is_closure y g1 == is_closure y g /\
               wosize_of_object y g1 == wosize_of_object y g)
      = color_change_preserves_wosize_any t y g Header.Gray;
        color_change_preserves_is_closure t y g Header.Gray;
        if y <> t then begin
          color_change_preserves_other_is_no_scan t y g Header.Gray;
          color_change_preserves_other_color t y g Header.Gray;
          is_blue_iff y g; is_blue_iff y g1
        end else
          color_preserves_is_no_scan t g Header.Gray
    in
    FStar.Classical.forall_intro col;
    let rd (b: hp_addr) : Lemma (hd_address t <> b ==> read_word g1 b == read_word g b)
      = if hd_address t <> b then color_change_preserves_other_read t b g Header.Gray
    in
    FStar.Classical.forall_intro rd;
    // the free list: the same cells, with the same links
    let cells (c: U64.t) : Lemma (FL.fl_cell g1 c <==> FL.fl_cell g c) = () in
    FStar.Classical.forall_intro cells;
    let links (c: U64.t)
      : Lemma (requires FL.fl_cell g c) (ensures FL.fl_next g1 c == FL.fl_next g c)
      = FLA.fl_cell_facts g c;
        let o : obj_addr = c in
        // the link is the cell's first field, strictly inside its block, so
        // not `t`'s header, which is a position of the walk
        SPI.obj_pos g o;
        SPI.obj_pos g t;
        SPI.colour_of g o;
        if hd_address t = c then SPU.no_pos_inside g (hd_address o) (U64.v c)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires links);
    FLA.fl_ascending_transfer g g1 fp
#pop-options

/// `MM.darken` keeps the same, and the darkened block is the old value's
/// target.
let darken_facts (g: heap) (fp: U64.t) (w: U64.t)
  : Lemma (requires walk_ok g fp)
          (ensures (let g1 = MM.darken g w in
                    walk_ok g1 fp /\
                    objects zero_addr g1 == objects zero_addr g /\
                    (forall (y: obj_addr). in_use free_stw g1 y == in_use free_stw g y) /\
                    (forall (y: obj_addr).
                       is_no_scan y g1 == is_no_scan y g /\ is_closure y g1 == is_closure y g /\
                       wosize_of_object y g1 == wosize_of_object y g) /\
                    (forall (b: hp_addr).
                       (forall (t: obj_addr). Seq.mem t (objects zero_addr g) ==> hd_address t <> b) ==>
                       read_word g1 b == read_word g b)))
  = if is_pointer w &&
       Seq.mem (resolve_object (w <: obj_addr) g) (objects zero_addr g) &&
       is_white (resolve_object (w <: obj_addr) g) g
    then grey_facts g fp (resolve_object (w <: obj_addr) g)

/// ---------------------------------------------------------------------------
/// The collector's state
/// ---------------------------------------------------------------------------

/// Idle: the stop-the-world shape.
#push-options "--z3rlimit 30"
let modify_idle (minor: minor_state) (g: heap) (fp: U64.t) (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires GenInv.collection_heap_shape minor g fp /\ SPM.program_write free_stw g x a v)
          (ensures GenInv.collection_heap_shape minor (write_word g a v) fp)
  = let g' = write_word g a v in
    free_stw_ok ();
    free_def_ok_elim free_stw;
    GenInv.collection_heap_shape_elim minor g fp;
    GenInv.major_heap_shape_elim g fp;
    body_write_facts g fp x a v;
    MM.write_wf g x a v;
    MM.write_heads g x a v;
    PCS.free_list_shape_of_ascending g' fp;
    let ng (y: obj_addr) : Lemma (Seq.mem y (objects zero_addr g) ==> ~(is_gray y g))
      = if Seq.mem y (objects zero_addr g) then SweepInv.no_gray_elim y g
    in
    FStar.Classical.forall_intro ng;
    SweepInv.no_gray_intro g';
    GenInv.major_heap_shape_intro g' fp;
    GenInv.minor_major_fields_not_free_stw minor g;
    GenInv.minor_major_fields_not_free_stw minor g';
    mmf_transport free_stw minor g g';
    GenInv.collection_heap_shape_intro minor g' fp
#pop-options

/// Mid-sweep: the sweep phase (`SPM.write_sweep_phase`).
#push-options "--z3rlimit 20"
let modify_sweeping (minor: minor_state) (g: heap) (fp: U64.t) (c: U64.t)
  (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires GI.phase_shape minor g fp (Ph.Sweeping c) /\
                    SPM.program_write (SPI.free_incremental c) g x a v)
          (ensures GI.phase_shape minor (write_word g a v) fp (Ph.Sweeping c))
  = let g' = write_word g a v in
    GI.phase_shape_sweeping minor g fp c;
    GI.phase_shape_sweeping minor g' fp c;
    SPI.free_incremental_ok c;
    free_def_ok_elim (SPI.free_incremental c);
    SPM.write_sweep_phase g fp c x a v;
    SPI.sweep_inv_incremental_iff g fp c;
    SPI.sweep_shape_elim g fp c;
    body_write_facts g fp x a v;
    mmf_transport (SPI.free_incremental c) minor g g'
#pop-options

/// While marking: the deletion barrier (`MM.marking_write_barrier`) and the
/// minor collection's shape at `free_stw`.
#push-options "--z3rlimit 30"
let modify_marking (minor: minor_state) (g: heap) (fp: U64.t) (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires GI.phase_shape minor g fp Ph.Marking /\
                    SPM.program_write free_stw g x a v /\
                    (~(is_no_scan x g) ==> MM.target_ok g (GMM.nursery_held minor) v))
          (ensures GI.phase_shape minor (write_word (MM.darken g (read_word g a)) a v) fp Ph.Marking)
  = let held = GMM.nursery_held minor in
    let g1 = MM.darken g (read_word g a) in
    let g' = write_word g1 a v in
    GI.phase_shape_marking minor g fp;
    GI.phase_shape_marking minor g' fp;
    free_stw_ok ();
    free_def_ok_elim free_stw;
    GenInv.collection_shape_with_elim Ph.Marking free_stw minor g fp;
    GenInv.major_shape_with_elim Ph.Marking free_stw g fp;
    MM.marking_write_barrier g held x a v;
    darken_facts g fp (read_word g a);
    body_write_facts g1 fp x a v;
    PCS.free_list_shape_of_ascending g' fp;
    GenInv.major_shape_with_intro Ph.Marking free_stw g' fp;
    mmf_transport free_stw minor g g1;
    mmf_transport free_stw minor g1 g';
    GenInv.collection_shape_with_intro Ph.Marking free_stw minor g' fp
#pop-options

let modify_phase_shape ph minor g fp x a v =
  match ph with
  | Ph.Idle ->
      GI.phase_free_idle ();
      GI.phase_shape_idle minor g fp;
      GI.phase_shape_idle minor (write_word g a v) fp;
      modify_idle minor g fp x a v
  | Ph.Marking ->
      GI.phase_free_marking ();
      modify_marking minor g fp x a v
  | Ph.Sweeping c ->
      GI.phase_free_sweeping c;
      modify_sweeping minor g fp c x a v

/// The index of the field at a body word.
let slot_index (g: heap) (x: obj_addr) (a: hp_addr)
  : Ghost nat (requires SPM.in_body g x a)
              (ensures fun j -> U64.v x + j * 8 == U64.v a /\ j < U64.v (wosize_of_object x g) /\
                             U64.v x + j * 8 + 8 <= heap_size)
  = FStar.Math.Lemmas.lemma_div_exact (U64.v a - U64.v x) 8;
    (U64.v a - U64.v x) / 8

/// The old value of a field of a non-free scannable block, if a major
/// pointer, points into the walk.
let old_target (free: free_def) (g: heap) (x: obj_addr) (a: hp_addr)
  : Lemma (requires free_def_ok free /\ well_formed_heap_with free g /\ in_use free g x /\
                    scannable g x /\ SPM.in_body g x a)
          (ensures is_pointer (read_word g a) ==>
                   Seq.mem (resolve_object (read_word g a <: obj_addr) g) (objects zero_addr g))
  = if is_pointer (read_word g a) then begin
      let j = slot_index g x a in
      GC.Spec.FieldTarget.wf_with_field free g x j;
      free_def_ok_elim free
    end

#push-options "--z3rlimit 30"
let modify_heap_facts ph minor g fp x a v =
  shape_facts ph minor g fp;
  let free = GI.phase_free ph in
  free_def_ok_elim free;
  (if is_pointer (read_word g a) then begin
     let j = slot_index g x a in
     GC.Spec.FieldTarget.wf_with_field free g x j
   end);
  if not (Ph.Marking? ph) then body_write_facts g fp x a v
#pop-options

#push-options "--z3rlimit 30"
let modify_mark_cache ph minor g fp x a v st ov p cap =
  modify_heap_facts ph minor g fp x a v;
  let old = read_word g a in
  if Ph.Marking? ph then begin
    GI.phase_free_marking ();
    free_def_ok_elim free_stw;
    shape_facts ph minor g fp;
    GI.phase_shape_marking minor g fp;
    let g1 = MM.darken g old in
    MM.darken_inv g (GMM.nursery_held minor) old;
    MS.mark_cache_darken g st ov p old cap;
    darken_facts g fp old;
    let st' = if MS.darken_target g old && Seq.length st < cap
              then Seq.cons (resolve_object (old <: obj_addr) g) st else st in
    MS.mark_cache_barrier_write g1 st' (ov || Seq.length st = cap) p x a v
  end else begin
    shape_facts ph minor g fp;
    MS.mark_cache_off g (modify_heap ph g a v) ph ph st ov p
  end
#pop-options

/// ---------------------------------------------------------------------------
/// The remembered set
/// ---------------------------------------------------------------------------

/// The field `j` of `obj` is the word `a` or not.
let field_addr (obj: obj_addr) (j: nat{U64.v obj + j * 8 + 8 <= heap_size}) : hp_addr =
  U64.uint_to_t (U64.v obj + j * 8)

/// The only new entry is the slot.
let appended_new (b: bool) (a: U64.t) (sl: seq U64.t) (n: nat) (sl': seq U64.t) (n': nat) (i: nat)
  : Lemma (requires appended b a sl n sl' n' /\ n <= i /\ i < n')
          (ensures b /\ i == n /\ Seq.index sl' i == a)
  = ()

/// An entry of the old table is one of the new.
let covered_prefix (sl sl': seq U64.t) (n: nat{n <= Seq.length sl}) (n': nat{n' <= Seq.length sl'}) (addr: nat)
  : Lemma (requires n <= Seq.length sl /\ n <= n' /\ n' <= Seq.length sl' /\
                    (exists (i: nat). i < n /\ U64.v (Seq.index sl i) == addr) /\
                    (forall (i: nat). i < n ==> Seq.index sl' i == Seq.index sl i))
          (ensures exists (i: nat). i < n' /\ U64.v (Seq.index sl' i) == addr)
  = eliminate exists (i: nat). i < n /\ U64.v (Seq.index sl i) == addr
    with assert (U64.v (Seq.index sl' i) == addr)

/// The coverage clause at one field.
let covers_at (free: free_def) (g: heap) (sl: seq U64.t) (n: nat{n <= Seq.length sl}) (obj: obj_addr) (j: nat)
  : Lemma (requires n <= Seq.length sl /\ RT.ref_table_covers_with free g sl n /\
                    is_block g obj /\ not (free g obj) /\ scannable g obj /\
                    j < U64.v (wosize_of_object obj g) /\ U64.v obj + j * 8 + 8 <= heap_size /\
                    Promote.is_minor_pointer (GB.to_minor_offset
                      (read_word g (U64.uint_to_t (U64.v obj + j * 8)))))
          (ensures exists (i: nat). i < n /\ U64.v (Seq.index sl i) == U64.v obj + j * 8)
  = ()

/// A field of a non-free scannable block, as the soundness clause states it.
let slot_of (free: free_def) (g: heap) (addr: nat) : prop =
  exists (obj: obj_addr) (j: nat).
    is_block g obj /\ not (free g obj) /\ scannable g obj /\
    j < U64.v (wosize_of_object obj g) /\ addr == U64.v obj + j * 8

let slot_of_transport (free: free_def) (g g': heap) (addr: nat)
  : Lemma (requires slot_of free g addr /\
                    (forall (obj: obj_addr). in_use free g obj ==>
                       in_use free g' obj /\ scannable g' obj == scannable g obj /\
                       wosize_of_object obj g' == wosize_of_object obj g))
          (ensures slot_of free g' addr)
  = eliminate exists (obj: obj_addr) (j: nat).
      is_block g obj /\ not (free g obj) /\ scannable g obj /\
      j < U64.v (wosize_of_object obj g) /\ addr == U64.v obj + j * 8
    with introduce exists (obj: obj_addr) (j: nat).
      is_block g' obj /\ not (free g' obj) /\ scannable g' obj /\
      j < U64.v (wosize_of_object obj g') /\ addr == U64.v obj + j * 8
    with obj j and ()

let sound_elim (free: free_def) (g: heap) (sl: seq U64.t) (n: nat{n <= Seq.length sl}) (i: nat)
  : Lemma (requires n <= Seq.length sl /\ RT.ref_table_sound_with free g sl n /\ i < n)
          (ensures U64.v (Seq.index sl i) < heap_size /\ U64.v (Seq.index sl i) % 8 == 0 /\
                   slot_of free g (U64.v (Seq.index sl i)))
  = ()

let sound_intro (free: free_def) (g: heap) (sl: seq U64.t) (n: nat{n <= Seq.length sl})
  (h: (i: nat) -> Lemma (requires i < n /\ n <= Seq.length sl)
                       (ensures U64.v (Seq.index sl i) < heap_size /\ U64.v (Seq.index sl i) % 8 == 0 /\
                                slot_of free g (U64.v (Seq.index sl i))))
  : Lemma (requires n <= Seq.length sl) (ensures RT.ref_table_sound_with free g sl n)
  = let aux (i: nat)
      : Lemma (i < n ==> U64.v (Seq.index sl i) < heap_size /\ U64.v (Seq.index sl i) % 8 == 0 /\
                         slot_of free g (U64.v (Seq.index sl i)))
      = if i < n then h i
    in
    FStar.Classical.forall_intro aux

let covers_intro (free: free_def) (g: heap) (sl: seq U64.t) (n: nat{n <= Seq.length sl})
  (h: (obj: obj_addr) -> (j: nat) ->
      Lemma (requires n <= Seq.length sl /\ is_block g obj /\ not (free g obj) /\ scannable g obj /\
                      j < U64.v (wosize_of_object obj g) /\ U64.v obj + j * 8 + 8 <= heap_size /\
                      Promote.is_minor_pointer (GB.to_minor_offset
                        (read_word g (U64.uint_to_t (U64.v obj + j * 8)))))
            (ensures exists (i: nat). i < n /\ U64.v (Seq.index sl i) == U64.v obj + j * 8))
  : Lemma (requires n <= Seq.length sl) (ensures RT.ref_table_covers_with free g sl n)
  = FStar.Classical.forall_intro_2 (fun obj -> FStar.Classical.move_requires (h obj))

#push-options "--z3rlimit 20"
let write_ref_table free g x a v b sl sl' n n' =
  let g' = write_word g a v in
  assert (n <= n' /\ n' <= Seq.length sl');
  free_def_ok_elim free;
  MM.write_heads g x a v;
  SPI.same_heads_facts g g';
  let keep (obj: obj_addr)
    : Lemma (in_use free g' obj == in_use free g obj /\
             (in_use free g obj ==> scannable g' obj == scannable g obj /\
                                    wosize_of_object obj g' == wosize_of_object obj g))
    = if in_use free g obj then MM.header_kept_facts g g' obj
  in
  FStar.Classical.forall_intro keep;
  // coverage
  let cov (obj: obj_addr) (j: nat)
    : Lemma (requires is_block g' obj /\ not (free g' obj) /\ scannable g' obj /\
                      j < U64.v (wosize_of_object obj g') /\ U64.v obj + j * 8 + 8 <= heap_size /\
                      Promote.is_minor_pointer (GB.to_minor_offset
                        (read_word g' (U64.uint_to_t (U64.v obj + j * 8)))))
            (ensures exists (i: nat). i < n' /\ U64.v (Seq.index sl' i) == U64.v obj + j * 8)
    = keep obj;
      let fa = field_addr obj j in
      if fa = a then begin
        read_write_same g a v;
        if b then assert (U64.v (Seq.index sl' n) == U64.v obj + j * 8)
        else begin
          covers_at free g sl n obj j;
          covered_prefix sl sl' n n' (U64.v obj + j * 8)
        end
      end else begin
        read_write_different g a fa v;
        covers_at free g sl n obj j;
        covered_prefix sl sl' n n' (U64.v obj + j * 8)
      end
  in
  covers_intro free g' sl' n' cov;
  // soundness
  let snd_ok (i: nat)
    : Lemma (requires i < n')
            (ensures U64.v (Seq.index sl' i) < heap_size /\ U64.v (Seq.index sl' i) % 8 == 0 /\
                     slot_of free g' (U64.v (Seq.index sl' i)))
    = if i < n then begin
        sound_elim free g sl n i;
        slot_of_transport free g g' (U64.v (Seq.index sl i))
      end else begin
        appended_new b a sl n sl' n' i;
        let j = slot_index g x a in
        keep x;
        MM.header_kept_facts g g' x;
        introduce exists (obj: obj_addr) (j: nat).
          is_block g' obj /\ not (free g' obj) /\ scannable g' obj /\
          j < U64.v (wosize_of_object obj g') /\ U64.v a == U64.v obj + j * 8
        with x j and ()
      end
  in
  sound_intro free g' sl' n' snd_ok
#pop-options

/// Darkening keeps the remembered set: no field of a non-free block is a
/// header.
#push-options "--z3rlimit 20"
let darken_ref_table (g: heap) (fp: U64.t) (w: U64.t) (sl: seq U64.t) (n: nat)
  : Lemma (requires walk_ok g fp /\
                    RT.ref_table_covers_with free_stw g sl n /\ RT.ref_table_sound_with free_stw g sl n)
          (ensures RT.ref_table_covers_with free_stw (MM.darken g w) sl n /\
                   RT.ref_table_sound_with free_stw (MM.darken g w) sl n)
  = let g1 = MM.darken g w in
    free_stw_ok ();
    free_def_ok_elim free_stw;
    darken_facts g fp w;
    let fld (obj: obj_addr) (j: nat)
      : Lemma (requires in_use free_stw g obj /\ j < U64.v (wosize_of_object obj g) /\
                        U64.v obj + j * 8 + 8 <= heap_size)
              (ensures read_word g1 (U64.uint_to_t (U64.v obj + j * 8)) ==
                       read_word g (U64.uint_to_t (U64.v obj + j * 8)))
      = let fa = field_addr obj j in
        assert (SPM.in_body g obj fa);
        let nh (t: obj_addr)
          : Lemma (Seq.mem t (objects zero_addr g) ==> hd_address t <> fa)
          = if Seq.mem t (objects zero_addr g) then body_not_header g obj t fa
        in
        FStar.Classical.forall_intro nh
    in
    let cov (obj: obj_addr) (j: nat)
      : Lemma (requires is_block g1 obj /\ not (free_stw g1 obj) /\ scannable g1 obj /\
                        j < U64.v (wosize_of_object obj g1) /\ U64.v obj + j * 8 + 8 <= heap_size /\
                        Promote.is_minor_pointer (GB.to_minor_offset
                          (read_word g1 (U64.uint_to_t (U64.v obj + j * 8)))))
              (ensures exists (i: nat). i < n /\ U64.v (Seq.index sl i) == U64.v obj + j * 8)
      = assert (in_use free_stw g1 obj);
        fld obj j;
        covers_at free_stw g sl n obj j
    in
    covers_intro free_stw g1 sl n cov;
    let snd_ok (i: nat)
      : Lemma (requires i < n)
              (ensures U64.v (Seq.index sl i) < heap_size /\ U64.v (Seq.index sl i) % 8 == 0 /\
                       slot_of free_stw g1 (U64.v (Seq.index sl i)))
      = sound_elim free_stw g sl n i;
        slot_of_transport free_stw g g1 (U64.v (Seq.index sl i))
    in
    sound_intro free_stw g1 sl n snd_ok
#pop-options

#push-options "--z3rlimit 30"
let modify_ref_table ph minor g fp x a v sl sl' n n' =
  shape_facts ph minor g fp;
  let free = GI.phase_free ph in
  free_def_ok_elim free;
  if Ph.Marking? ph then begin
    GI.phase_free_marking ();
    free_stw_ok ();
    let old = read_word g a in
    let g1 = MM.darken g old in
    darken_facts g fp old;
    darken_ref_table g fp old sl n;
    old_target free_stw g x a;
    // the slot is no header, so the darkening left it alone
    let nh (t: obj_addr) : Lemma (Seq.mem t (objects zero_addr g) ==> hd_address t <> a)
      = if Seq.mem t (objects zero_addr g) then body_not_header g x t a
    in
    FStar.Classical.forall_intro nh;
    assert (read_word g1 a == old);
    assert (SPM.in_body g1 x a);
    write_ref_table free_stw g1 x a v (modify_records g a v) sl sl' n n'
  end else
    write_ref_table free g x a v (modify_records g a v) sl sl' n n'
#pop-options

let initialize_ref_table free g x a v sl sl' n n' =
  write_ref_table free g x a v (initialize_records v) sl sl' n n'
