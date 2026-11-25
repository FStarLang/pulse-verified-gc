/// ---------------------------------------------------------------------------
/// GC.Gen.Run.Invariant.MajorAlloc - a direct major allocation keeps the run
/// invariant
/// ---------------------------------------------------------------------------
///
/// From the relational step alone (`major_alloc_step`, properties (1)-(4)
/// and the walk's end), not from the allocator: the new block `a` was free
/// memory, so it was not an allocated block (`a_fresh`), and every other
/// block keeps whether it is allocated, its header and its fields
/// (`GC.Gen.Run.Invariant.Allocator.frame`).  The history adds `a` to the
/// blocks allocated since, so the kept blocks are the old ones and `a`.
///
///   * the collector's state is (4); the remembered set gains `a`'s young
///     slots (`young_slots`), fields of a scannable block not free at the
///     phase;
///   * B1: the old blocks keep their edges, and `a`'s fields point (resolved)
///     at kept blocks (`stores_in_kept`); well-formedness is transported with
///     `a` counted free, then closed (`close_fresh`);
///   * B2-B5 and the phase's clauses: `a` is new, black while marking and in
///     front of the cursor, and its words were free (B5 through
///     `new_word`: with the walk's end kept, a free word after lay in a free
///     block before).

module GC.Gen.Run.Invariant.MajorAlloc

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.MinorHeap
open GC.Gen.Run.Step
open GC.Gen.Run.History

module U64 = FStar.UInt64
module Ph = GC.Spec.Phase
module MP = GC.Spec.MarkPhase
module MM = GC.Spec.MarkPhase.Mutator
module MPA = GC.Spec.MarkPhase.Alloc
module MPC = GC.Spec.MarkPhase.Completeness
module SPC = GC.Spec.SweepPhase.Completeness
module SPI = GC.Spec.SweepPhase.Intrinsic
module SPM = GC.Spec.SweepPhase.Mutator
module LL = GC.Spec.FusedSweep.Lossless
module W = GC.Spec.Walk
module GI = GC.Gen.Incremental
module GBase = GC.Gen.Base
module Promote = GC.Gen.Promote
module RT = GC.Gen.RefTable
module GenInv = GC.Gen.HeapInvariant
module Mark = GC.Spec.Mark
module Header = GC.Lib.Header
module D = GC.Gen.Run.Invariant.Defs
module WR = GC.Gen.Run.Invariant.Write
module AL = GC.Gen.Run.Invariant.Allocator
module I = GC.Model.Ideal

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The step, with its block named
/// ---------------------------------------------------------------------------

let mctx (r: real_state) (tag: I.tag_t) (size: nat) (init: seq U64.t) (r': real_state) (a: obj_addr) : prop =
  size >= 1 /\ Seq.length init == size /\ tag <> infix_tag /\ init_storable r tag init /\
  r'.memory.nursery == r.memory.nursery /\ r'.phase == r.phase /\ r'.scan_pos == r.scan_pos /\
  was_free r.memory.major r'.memory.major a /\
  is_allocated r'.memory (Major a) /\
  tag_of_object a r'.memory.major == tag /\ U64.v (wosize_of_object a r'.memory.major) == size /\
  color_of_object a r'.memory.major == Ph.allocation_color r.phase (hd_address a) /\
  (forall (i: nat). i < size ==> block_field r'.memory (Major a) i == Seq.index init i) /\
  (forall (x: obj_addr). x <> a ==>
     (is_allocated r.memory (Major x) <==> is_allocated r'.memory (Major x)) /\
     (is_allocated r.memory (Major x) ==> same_block r.memory.major r'.memory.major x)) /\
  r'.ref_table == (if I.tag_scannable tag then Seq.append r.ref_table (young_slots a init)
                   else r.ref_table) /\
  W.walk_end r'.memory.major zero_addr == W.walk_end r.memory.major zero_addr /\
  GI.phase_shape r'.memory.nursery r'.memory.major r'.free_list r'.phase r'.scan_pos /\
  D.phase_shape r

/// The new block was not an allocated block: its words were free.
#push-options "--z3rlimit 30"
let a_fresh (r: real_state) (tag: I.tag_t) (size: nat) (init: seq U64.t) (r': real_state) (a: obj_addr)
  : Lemma (requires mctx r tag size init r' a)
          (ensures AL.frame r.memory.major r'.memory.major a)
  = let g = r.memory.major in
    let g' = r'.memory.major in
    hd_address_spec a;
    assert (LL.in_extent g' a (U64.v (hd_address a)));
    assert (LL.blue_covered g (U64.v (hd_address a)));
    if Seq.mem a (objects zero_addr g) && not (is_blue a g) then begin
      eliminate exists (y: obj_addr). Seq.mem y (objects zero_addr g) /\ is_blue y g /\
                                      LL.in_extent g y (U64.v (hd_address a))
      with SPC.extents_disjoint g y a (U64.v (hd_address a))
    end
#pop-options

/// The blocks the step made: `a`.
let made_a (r: real_state) (r': real_state) (a: obj_addr)
  : Lemma (requires AL.frame r.memory.major r'.memory.major a)
          (ensures forall (x: obj_addr). made r r' x <==> x == a)
  = ()

/// ---------------------------------------------------------------------------
/// The young slots
/// ---------------------------------------------------------------------------

#push-options "--fuel 1 --z3rlimit 20"
let rec young_slots_index (a: obj_addr) (init: seq U64.t) (i: nat) (k: nat)
  : Lemma (requires k < Seq.length (young_slots_from a init i))
          (ensures exists (j: nat). i <= j /\ j < Seq.length init /\ is_young (Seq.index init j) /\
                     Seq.index (young_slots_from a init i) k == major_slot a j)
          (decreases (Seq.length init - i))
  = if i >= Seq.length init then ()
    else begin
      let rest = young_slots_from a init (i + 1) in
      if is_young (Seq.index init i) then begin
        if k = 0 then () else young_slots_index a init (i + 1) (k - 1)
      end else young_slots_index a init (i + 1) k
    end

let rec young_slots_mem (a: obj_addr) (init: seq U64.t) (i: nat) (j: nat)
  : Lemma (requires i <= j /\ j < Seq.length init /\ is_young (Seq.index init j))
          (ensures exists (k: nat). k < Seq.length (young_slots_from a init i) /\
                     Seq.index (young_slots_from a init i) k == major_slot a j)
          (decreases (Seq.length init - i))
  = if i = j then ()
    else begin
      young_slots_mem a init (i + 1) j;
      if is_young (Seq.index init i) then begin
        let rest = young_slots_from a init (i + 1) in
        eliminate exists (k: nat). k < Seq.length rest /\ Seq.index rest k == major_slot a j
        with (assert (Seq.index (Seq.cons (major_slot a i) rest) (k + 1) == Seq.index rest k))
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// The remembered set
/// ---------------------------------------------------------------------------

let rt_new (r r': real_state) (tag: I.tag_t) (a: obj_addr) (init: seq U64.t) : prop =
  r'.ref_table == (if I.tag_scannable tag then Seq.append r.ref_table (young_slots a init)
                   else r.ref_table)

/// The new block, as a block of `g'`.
let new_ok (free: free_def) (g': heap) (a: obj_addr) (tag: I.tag_t) (init: seq U64.t) : prop =
  in_use free g' a /\ tag_of_object a g' == tag /\
  U64.v (wosize_of_object a g') == Seq.length init /\
  U64.v a + 8 * Seq.length init <= heap_size /\
  (forall (i: nat). i < Seq.length init ==> major_field g' a i == Seq.index init i)

/// The old blocks under `free`, after.
let old_ok (free: free_def) (g g': heap) (a: obj_addr) : prop =
  (forall (y: obj_addr). in_use free g y ==>
     y <> a /\ in_use free g' y /\ read_word g' (hd_address y) == read_word g (hd_address y) /\
     (forall (i: nat). i < U64.v (wosize_of_object y g) ==> major_field g' y i == major_field g y i)) /\
  (forall (y: obj_addr). y <> a /\ in_use free g' y ==> in_use free g y)

let old_ok_intro (free: free_def) (g g': heap) (a: obj_addr)
  : Lemma (requires AL.frame g g' a /\ free_def_ok free)
          (ensures old_ok free g g' a)
  = let one (y: obj_addr)
      : Lemma ((in_use free g y ==>
                  y <> a /\ in_use free g' y /\ read_word g' (hd_address y) == read_word g (hd_address y) /\
                  (forall (i: nat). i < U64.v (wosize_of_object y g) ==> major_field g' y i == major_field g y i)) /\
               (y <> a /\ in_use free g' y ==> in_use free g y))
      = AL.frame_in_use free g g' a y;
        free_def_ok_elim free
    in
    FStar.Classical.forall_intro one

let same_header_facts (g g': heap) (y: obj_addr)
  : Lemma (requires read_word g' (hd_address y) == read_word g (hd_address y))
          (ensures wosize_of_object y g' == wosize_of_object y g /\ tag_of_object y g' == tag_of_object y g /\
                   scannable g' y == scannable g y /\ color_of_object y g' == color_of_object y g /\
                   (is_blue y g' <==> is_blue y g) /\ (is_white y g' <==> is_white y g) /\
                   (is_black y g' <==> is_black y g) /\ (is_gray y g' <==> is_gray y g))
  = SPI.colour_of g y; SPI.colour_of g' y;
    is_no_scan_spec y g; is_no_scan_spec y g';
    color_of_object_spec y g; color_of_object_spec y g';
    is_gray_iff y g; is_gray_iff y g'

/// The address of field `j` of `a`, without its wrap-around.
let major_slot_v (a: obj_addr) (j: nat)
  : Lemma (requires U64.v a + 8 * j < pow2 64)
          (ensures U64.v (major_slot a j) == U64.v a + j * 8)
  = FStar.Math.Lemmas.small_mod (U64.v a + 8 * j) (pow2 64)

#push-options "--z3rlimit 40"
let rt_sound (free: free_def) (r r': real_state) (tag: I.tag_t) (a: obj_addr) (init: seq U64.t)
  : Lemma (requires old_ok free r.memory.major r'.memory.major a /\
                    new_ok free r'.memory.major a tag init /\ rt_new r r' tag a init /\
                    RT.ref_table_sound_with free r.memory.major r.ref_table (Seq.length r.ref_table))
          (ensures RT.ref_table_sound_with free r'.memory.major r'.ref_table (Seq.length r'.ref_table))
  = let g = r.memory.major in
    let g' = r'.memory.major in
    let rt = r.ref_table in
    let rt' = r'.ref_table in
    let n = Seq.length rt in
    let h (i: nat)
      : Lemma (requires i < Seq.length rt' /\ Seq.length rt' <= Seq.length rt')
              (ensures U64.v (Seq.index rt' i) < heap_size /\ U64.v (Seq.index rt' i) % 8 == 0 /\
                       WR.slot_of free g' (U64.v (Seq.index rt' i)))
      = if i < n then begin
          (if I.tag_scannable tag then Seq.lemma_index_app1 rt (young_slots a init) i);
          let tr (obj: obj_addr)
            : Lemma (in_use free g obj ==>
                       in_use free g' obj /\ scannable g' obj == scannable g obj /\
                       wosize_of_object obj g' == wosize_of_object obj g)
            = if in_use free g obj then same_header_facts g g' obj in
          FStar.Classical.forall_intro tr;
          WR.slot_of_transport free g g' (U64.v (Seq.index rt i))
        end else begin
          assert (I.tag_scannable tag);
          Seq.lemma_index_app2 rt (young_slots a init) i;
          young_slots_index a init 0 (i - n);
          eliminate exists (j: nat). j < Seq.length init /\ is_young (Seq.index init j) /\
                                     Seq.index (young_slots a init) (i - n) == major_slot a j
          with begin
            is_no_scan_spec a g';
            major_slot_v a j;
            assert (U64.v (major_slot a j) == U64.v a + j * 8);
            assert (U64.v (Seq.index rt' i) == U64.v a + j * 8);
            FStar.Math.Lemmas.lemma_mod_plus (U64.v a) j 8;
            introduce exists (obj: obj_addr) (j': nat).
              is_block g' obj /\ not (free g' obj) /\ scannable g' obj /\
              j' < U64.v (wosize_of_object obj g') /\ U64.v (Seq.index rt' i) == U64.v obj + j' * 8
            with a j and ()
          end
        end
    in
    WR.sound_intro free g' rt' (Seq.length rt') h
#pop-options

#push-options "--z3rlimit 40"
let rt_covers (free: free_def) (r r': real_state) (tag: I.tag_t) (a: obj_addr) (init: seq U64.t)
  : Lemma (requires old_ok free r.memory.major r'.memory.major a /\
                    new_ok free r'.memory.major a tag init /\ rt_new r r' tag a init /\
                    RT.ref_table_covers_with free r.memory.major r.ref_table (Seq.length r.ref_table))
          (ensures RT.ref_table_covers_with free r'.memory.major r'.ref_table (Seq.length r'.ref_table))
  = let g = r.memory.major in
    let g' = r'.memory.major in
    let rt = r.ref_table in
    let rt' = r'.ref_table in
    let n = Seq.length rt in
    let h (obj: obj_addr) (j: nat)
      : Lemma (requires Seq.length rt' <= Seq.length rt' /\ is_block g' obj /\ not (free g' obj) /\ scannable g' obj /\
                        j < U64.v (wosize_of_object obj g') /\ U64.v obj + j * 8 + 8 <= heap_size /\
                        Promote.is_minor_pointer (GBase.to_minor_offset
                          (read_word g' (U64.uint_to_t (U64.v obj + j * 8)))))
              (ensures exists (i: nat). i < Seq.length rt' /\ U64.v (Seq.index rt' i) == U64.v obj + j * 8)
      = if obj = a then begin
          is_no_scan_spec a g';
          assert (major_field g' a j == Seq.index init j);
          young_slots_mem a init 0 j;
          FStar.Math.Lemmas.small_mod (U64.v a + 8 * j) (pow2 64);
          eliminate exists (k: nat). k < Seq.length (young_slots a init) /\
                                     Seq.index (young_slots a init) k == major_slot a j
          with begin
            Seq.lemma_index_app2 rt (young_slots a init) (n + k);
            introduce exists (i: nat). i < Seq.length rt' /\ U64.v (Seq.index rt' i) == U64.v obj + j * 8
            with (n + k) and ()
          end
        end else begin
          assert (in_use free g obj);
          same_header_facts g g' obj;
          assert (major_field g' obj j == major_field g obj j);
          eliminate exists (i: nat). i < n /\ U64.v (Seq.index rt i) == U64.v obj + j * 8
          with begin
            (if I.tag_scannable tag then Seq.lemma_index_app1 rt (young_slots a init) i);
            introduce exists (i: nat). i < Seq.length rt' /\ U64.v (Seq.index rt' i) == U64.v obj + j * 8
            with i and ()
          end
        end
    in
    WR.covers_intro free g' rt' (Seq.length rt') h
#pop-options

/// ---------------------------------------------------------------------------
/// B1: the kept blocks and `a`
/// ---------------------------------------------------------------------------

/// **Closing a fresh block**: well formed with `obj` counted free, and
/// `obj`'s fields storable, is well formed.
#push-options "--z3rlimit 30"
let close_fresh (free fresh_free: free_def) (g: heap) (obj: obj_addr)
  : Lemma (requires free_def_ok free /\ free_def_ok fresh_free /\
                    (forall (h: heap) (x: obj_addr). fresh_free h x == (free h x || x = obj)) /\
                    well_formed_heap_with fresh_free g /\
                    SPM.fields_storable free g obj)
          (ensures well_formed_heap_with free g)
  = wf_with_parts ();
    free_def_ok_elim free;
    free_def_ok_elim fresh_free;
    let closure (src: obj_addr) (j: nat)
      : Lemma (requires in_use free g src /\ ~(is_no_scan src g) /\
                        j < U64.v (wosize_of_object src g) /\ U64.v src + j * 8 + 8 <= heap_size)
              (ensures (let w = read_word g (U64.uint_to_t (U64.v src + j * 8)) in
                        is_pointer w ==>
                        in_use free g (resolve_object (w <: obj_addr) g) /\
                        infix_addr_wf g (objects zero_addr g) (w <: obj_addr)))
      = let w = read_word g (U64.uint_to_t (U64.v src + j * 8)) in
        if src = obj then assert (SPI.storable free g (SPM.field_val g obj j))
        else if is_pointer w then GC.Spec.FieldTarget.wf_with_field fresh_free g src j
    in
    pointer_clauses_from_field_closure free g closure
#pop-options

/// A value stored at the phase into a kept block stays storable there, for
/// the kept blocks with `a`.
#push-options "--z3rlimit 30"
let storable_after (pf: free_def) (s s': obj_addr -> prop) (g g': heap) (a: obj_addr) (v: U64.t)
  : Lemma (requires AL.frame g g' a /\ free_def_ok pf /\ well_formed_heap_with pf g /\
                    no_infix_block g /\ no_infix_block g' /\
                    SPI.storable pf g v /\ (is_pointer v ==> s (resolve_object (v <: obj_addr) g)) /\
                    (forall (x: obj_addr). s x ==> s' x))
          (ensures SPI.storable (MPC.outside_snapshot s') g' v)
  = if is_pointer v then begin
      AL.frame_keeps pf g g' a;
      SPI.storable_transfer g g' pf pf v;
      MPA.keeps_blocks_resolve pf g g' v;
      free_def_ok_elim pf;
      MPC.in_use_outside_snapshot s' g' (resolve_object (v <: obj_addr) g')
    end
#pop-options

/// In use for the kept blocks with `a` counted free after, exactly when in
/// use for the kept blocks before.
#push-options "--z3rlimit 30"
let in_use_kept_after (s s': obj_addr -> prop) (g g': heap) (a: obj_addr) (x: obj_addr)
  : Lemma (requires AL.frame g g' a /\ (forall (y: obj_addr). s' y <==> s y \/ y == a))
          (ensures in_use (MPC.outside_snapshot_or_new s' a) g' x == in_use (MPC.outside_snapshot s) g x /\
                   (in_use (MPC.outside_snapshot s) g x ==> SPI.same_block g g' (hd_address x)))
  = MPC.in_use_outside_snapshot s g x;
    MPC.in_use_outside_snapshot s' g' x;
    if x = a then ()
    else if Seq.mem x (objects zero_addr g) && not (is_blue x g) then begin
      same_header_facts g g' x;
      AL.spi_same_block g g' x
    end
#pop-options

/// B1 after: dark blocks are kept, kept blocks point at kept blocks.
#push-options "--z3rlimit 40"
let within_after (s s': obj_addr -> prop) (g g': heap) (a: obj_addr) (tag: I.tag_t) (init: seq U64.t)
  : Lemma (requires MPC.within_snapshot s g /\ (forall (y: obj_addr). s' y <==> s y \/ y == a) /\
                    AL.frame g g' a /\ no_infix_block g' /\
                    tag_of_object a g' == tag /\ U64.v (wosize_of_object a g') == Seq.length init /\
                    U64.v a + 8 * Seq.length init <= heap_size /\
                    (forall (i: nat). i < Seq.length init ==> major_field g' a i == Seq.index init i) /\
                    (I.tag_scannable tag ==>
                       (forall (i: nat). i < Seq.length init ==>
                          SPI.storable (MPC.outside_snapshot s') g' (Seq.index init i))))
          (ensures MPC.within_snapshot s' g')
  = let fo = MPC.outside_snapshot s in
    let fn = MPC.outside_snapshot_or_new s' a in
    let f' = MPC.outside_snapshot s' in
    MPC.outside_snapshot_ok s;
    MPC.outside_snapshot_ok s';
    MPC.outside_snapshot_or_new_ok s' a;
    // dark blocks
    let dark (x: obj_addr)
      : Lemma (Seq.mem x (objects zero_addr g') /\ (is_gray x g' \/ is_black x g') ==> s' x)
      = if x <> a && Seq.mem x (objects zero_addr g') && (is_gray x g' || is_black x g') then begin
          Mark.colors_exclusive x g';
          same_header_facts g g' x
        end
    in
    FStar.Classical.forall_intro dark;
    // well formed with `a` counted free, then closed
    FStar.Classical.forall_intro (FStar.Classical.move_requires (in_use_kept_after s s' g g' a));
    SPI.wf_transport g g' fo fn;
    is_no_scan_spec a g';
    let fs (i: nat)
      : Lemma (i < U64.v (wosize_of_object a g') /\ U64.v a + i * 8 + 8 <= heap_size /\ not (is_no_scan a g') ==>
               SPI.storable f' g' (SPM.field_val g' a i))
      = if i < U64.v (wosize_of_object a g') && U64.v a + i * 8 + 8 <= heap_size && not (is_no_scan a g')
        then assert (major_field g' a i == SPM.field_val g' a i)
    in
    FStar.Classical.forall_intro fs;
    assert (SPM.fields_storable f' g' a);
    assert (forall (h: heap) (x: obj_addr). fn h x == (f' h x || x = a));
    close_fresh f' fn g' a
#pop-options

/// ---------------------------------------------------------------------------
/// B2-B5
/// ---------------------------------------------------------------------------

/// The history after: `a` among the blocks allocated since.
let hist_ok (h h': cycle_history) (a: obj_addr) : prop =
  h'.start_memory == h.start_memory /\ h'.start_roots == h.start_roots /\
  (forall (x: obj_addr). h'.allocated_during_cycle x <==> h.allocated_during_cycle x \/ x == a)

let hist_facts (h h': cycle_history) (a: obj_addr)
  : Lemma (requires hist_ok h h' a)
          (ensures (forall (x: obj_addr). snapshot h' x <==> snapshot h x) /\
                   (forall (x: obj_addr). kept h' x <==> kept h x \/ x == a) /\
                   (forall (x: obj_addr). garbage_at_start h' x <==> garbage_at_start h x) /\
                   (forall (p: nat). reclaimable_at_start h' p <==> reclaimable_at_start h p))
  = ()

/// A block keeping its header keeps its extent.
let extent_same (g g': heap) (y: obj_addr) (p: nat)
  : Lemma (requires read_word g' (hd_address y) == read_word g (hd_address y))
          (ensures LL.in_extent g' y p <==> LL.in_extent g y p)
  = same_header_facts g g' y

/// B5 at a word.
#push-options "--z3rlimit 30"
let b5_word (h h': cycle_history) (g g': heap) (a: obj_addr) (p: nat)
  : Lemma (requires hist_ok h h' a /\ AL.frame g g' a /\ was_free g g' a /\
                    W.walk_end g' zero_addr == W.walk_end g zero_addr /\
                    W.walk_end g zero_addr + 8 >= heap_size /\
                    (forall (x: obj_addr). h.allocated_during_cycle x ==> Seq.mem x (objects zero_addr g) /\ ~(is_blue x g)) /\
                    (LL.blue_covered g' p \/ SPC.new_covered h'.allocated_during_cycle g' p))
          (ensures LL.blue_covered g p \/ SPC.new_covered h.allocated_during_cycle g p)
  = let one (y: obj_addr)
      : Lemma (requires Seq.mem y (objects zero_addr g') /\ LL.in_extent g' y p /\
                        (is_blue y g' \/ h'.allocated_during_cycle y))
              (ensures LL.blue_covered g p \/ SPC.new_covered h.allocated_during_cycle g p)
      = if y = a then ()
        else if h.allocated_during_cycle y then extent_same g g' y p
        else begin
          // a free block after, not allocated before
          SPC.extent_below_end g' y p;
          let z = SPC.block_over g p in
          if is_blue z g then ()
          else begin
            extent_same g g' z p;
            same_header_facts g g' z;
            SPC.extents_disjoint g' z y p
          end
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires one)
#pop-options

#push-options "--z3rlimit 40"
let base_after (h h': cycle_history) (m m': real_memory) (a: obj_addr)
  : Lemma (requires WR.base_ok h m /\ hist_ok h h' a /\ AL.frame m.major m'.major a /\
                    m'.nursery == m.nursery /\ was_free m.major m'.major a /\
                    W.walk_end m'.major zero_addr == W.walk_end m.major zero_addr /\
                    W.walk_end m.major zero_addr + 8 >= heap_size /\
                    no_infix_block m.major /\ no_infix_block m'.major)
          (ensures WR.base_ok h' m')
  = let g = m.major in
    let g' = m'.major in
    hist_facts h h' a;
    // the nursery points at kept blocks, through the same resolutions
    let free = MPC.outside_snapshot (kept h) in
    let free' = MPC.outside_snapshot (kept h') in
    MPC.outside_snapshot_ok (kept h);
    MPC.outside_snapshot_ok (kept h');
    AL.frame_keeps free g g' a;
    let iu (y: obj_addr)
      : Lemma (requires in_use free g y) (ensures in_use free' g' y)
      = MPC.in_use_outside_snapshot (kept h) g y;
        MPC.in_use_outside_snapshot (kept h') g' y;
        same_header_facts g g' y
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires iu);
    GenInv.minor_major_fields_not_free_transfer free free' m.nursery g g';
    // B2
    let b2 (x: obj_addr)
      : Lemma (requires snapshot h x)
              (ensures Seq.mem x (objects zero_addr g') /\ ~(is_blue x g') /\
                       wosize_of_object x g' == wosize_of_object x h.start_memory.major)
      = same_header_facts g g' x
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires b2);
    // B3, B4
    let b34 (x: obj_addr)
      : Lemma ((h'.allocated_during_cycle x ==> is_allocated m' (Major x) /\ ~(snapshot h' x)) /\
               (is_allocated m' (Major x) ==>
                  snapshot h' x \/ h'.allocated_during_cycle x \/ garbage_at_start h' x))
      = ()
    in
    FStar.Classical.forall_intro b34;
    // B5
    FStar.Classical.forall_intro (FStar.Classical.move_requires (b5_word h h' g g' a))
#pop-options

/// ---------------------------------------------------------------------------
/// The remembered slots, the added clauses, the phase's clause
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40"
let rt_kept_after (h h': cycle_history) (r r': real_state) (tag: I.tag_t) (a: obj_addr) (init: seq U64.t)
  : Lemma (requires WR.rt_kept_of h r.ref_table r.memory.major /\ WR.base_ok h r.memory /\
                    hist_ok h h' a /\ AL.frame r.memory.major r'.memory.major a /\ rt_new r r' tag a init /\
                    U64.v (wosize_of_object a r'.memory.major) == Seq.length init /\
                    U64.v a + 8 * Seq.length init <= heap_size)
          (ensures WR.rt_kept_of h' r'.ref_table r'.memory.major)
  = let g = r.memory.major in
    let g' = r'.memory.major in
    let rt = r.ref_table in
    let rt' = r'.ref_table in
    let n = Seq.length rt in
    hist_facts h h' a;
    let one (i: nat)
      : Lemma (i < Seq.length rt' ==>
               (exists (y: obj_addr) (j: nat). kept h' y /\ j < U64.v (wosize_of_object y g') /\
                  U64.v (Seq.index rt' i) == U64.v y + j * 8))
      = if i >= Seq.length rt' then ()
        else if i < n then begin
          (if I.tag_scannable tag then Seq.lemma_index_app1 rt (young_slots a init) i);
          eliminate exists (y: obj_addr) (j: nat). kept h y /\ j < U64.v (wosize_of_object y g) /\
              U64.v (Seq.index rt i) == U64.v y + j * 8
          with (WR.kept_mem h r.memory y;
                same_header_facts g g' y;
                introduce exists (y: obj_addr) (j: nat). kept h' y /\ j < U64.v (wosize_of_object y g') /\
                    U64.v (Seq.index rt' i) == U64.v y + j * 8
                with y j and ())
        end else begin
          assert (I.tag_scannable tag);
          Seq.lemma_index_app2 rt (young_slots a init) i;
          young_slots_index a init 0 (i - n);
          eliminate exists (j: nat). j < Seq.length init /\ is_young (Seq.index init j) /\
                                     Seq.index (young_slots a init) (i - n) == major_slot a j
          with begin
            FStar.Math.Lemmas.small_mod (U64.v a + 8 * j) (pow2 64);
            introduce exists (y: obj_addr) (j: nat). kept h' y /\ j < U64.v (wosize_of_object y g') /\
                U64.v (Seq.index rt' i) == U64.v y + j * 8
            with a j and ()
          end
        end
    in
    FStar.Classical.forall_intro one
#pop-options

/// The cursor of a sweep is a word boundary.
let sweep_cursor (minor: minor_state) (g: heap) (fp: U64.t) (c: U64.t) (sp: MP.scan_pos)
  : Lemma (requires GI.phase_shape minor g fp (Ph.Sweeping c) sp)
          (ensures U64.v c % 8 == 0)
  = GI.phase_shape_sweeping minor g fp c sp;
    SPI.sweep_inv_incremental_iff g fp c;
    SPI.sweep_shape_elim g fp c

/// The new block's colour: black while marking and at or in front of the
/// cursor, white otherwise.
let a_colour (g': heap) (ph: Ph.gc_phase) (a: obj_addr)
  : Lemma (requires color_of_object a g' == Ph.allocation_color ph (hd_address a))
          (ensures (Ph.Marking? ph ==> is_black a g') /\
                   (forall (c: U64.t). ph == Ph.Sweeping c /\ U64.v c % 8 == 0 ==>
                      (U64.v a > U64.v c ==> is_black a g') /\ (U64.v a <= U64.v c ==> is_white a g')) /\
                   (ph == Ph.Idle ==> is_white a g'))
  = hd_address_spec a;
    is_black_iff a g'; is_white_iff a g'

#push-options "--z3rlimit 40"
let blk_after (h h': cycle_history) (m m': real_memory) (ph: Ph.gc_phase) (a: obj_addr)
  : Lemma (requires WR.blk_extra h m ph /\ WR.base_ok h m /\ hist_ok h h' a /\ AL.frame m.major m'.major a /\
                    W.walk_end m'.major zero_addr == W.walk_end m.major zero_addr /\
                    color_of_object a m'.major == Ph.allocation_color ph (hd_address a) /\
                    (forall (c: U64.t). ph == Ph.Sweeping c ==> U64.v c % 8 == 0))
          (ensures WR.blk_extra h' m' ph)
  = let g = m.major in
    let g' = m'.major in
    hist_facts h h' a;
    a_colour g' ph a;
    let gs (x: obj_addr)
      : Lemma (garbage_at_start h' x /\ is_allocated m' (Major x) /\ ~(h'.allocated_during_cycle x) ==>
               wosize_of_object x g' == wosize_of_object x h.start_memory.major)
      = if x <> a && Seq.mem x (objects zero_addr g) && not (is_blue x g) then same_header_facts g g' x
    in
    FStar.Classical.forall_intro gs;
    match ph with
    | Ph.Sweeping c ->
        let bl (x: obj_addr) : Lemma (requires kept h' x /\ U64.v x > U64.v c) (ensures is_black x g')
          = if x <> a then begin WR.kept_mem h m x; same_header_facts g g' x end
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires bl)
    | _ -> ()
#pop-options

#push-options "--z3rlimit 40"
let phase_after (h h': cycle_history) (r r': real_state) (a: obj_addr)
  : Lemma (requires WR.phase_core r h /\ WR.base_ok h r.memory /\ hist_ok h h' a /\
                    AL.frame r.memory.major r'.memory.major a /\
                    r'.phase == r.phase /\ r'.scan_pos == r.scan_pos /\
                    color_of_object a r'.memory.major == Ph.allocation_color r.phase (hd_address a) /\
                    (Ph.Marking? r.phase ==> well_formed_heap r.memory.major /\ blocks_fit r'.memory.major))
          (ensures WR.phase_core r' h')
  = let g = r.memory.major in
    let g' = r'.memory.major in
    let sp = r.scan_pos in
    hist_facts h h' a;
    a_colour g' r.phase a;
    match r.phase with
    | Ph.Marking ->
        free_stw_ok ();
        free_def_ok_elim free_stw;
        AL.frame_keeps free_stw g g' a;
        let gw (y: obj_addr) : Lemma (MP.grey_or_white g y ==> in_use free_stw g y)
          = Mark.colors_exclusive y g in
        FStar.Classical.forall_intro gw;
        let reach (w: obj_addr)
          : Lemma (requires snapshot h w /\ Seq.mem w (objects zero_addr g') /\ is_white w g')
                  (ensures MP.marker_will_reach g' sp w)
          = Mark.colors_exclusive a g';
            Mark.colors_exclusive w g';
            same_header_facts g g' w;
            MPA.keeps_blocks_reach free_stw g g' sp w
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires reach);
        let blk (x: obj_addr) : Lemma (requires h'.allocated_during_cycle x) (ensures is_black x g')
          = if x <> a then same_header_facts g g' x
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires blk)
    | Ph.Sweeping c ->
        SPI.free_incremental_ok c;
        let iu (x: obj_addr) : Lemma (requires in_use (SPI.free_incremental c) g' x) (ensures kept h' x)
          = AL.frame_in_use (SPI.free_incremental c) g g' a x
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires iu)
    | Ph.Idle -> ()
#pop-options

/// The new block is not free at the phase.
#push-options "--z3rlimit 30"
let a_in_use (g': heap) (ph: Ph.gc_phase) (a: obj_addr)
  : Lemma (requires Seq.mem a (objects zero_addr g') /\ ~(is_blue a g') /\
                    color_of_object a g' == Ph.allocation_color ph (hd_address a) /\
                    (forall (c: U64.t). ph == Ph.Sweeping c ==> U64.v c % 8 == 0))
          (ensures in_use (GI.phase_free ph) g' a)
  = a_colour g' ph a;
    match ph with
    | Ph.Sweeping c -> Mark.colors_exclusive a g'
    | _ -> ()
#pop-options

/// With the nursery empty, so is the remembered set: a young initial value
/// names a nursery object.
#push-options "--z3rlimit 30"
let extra_after (r r': real_state) (tag: I.tag_t) (a: obj_addr) (init: seq U64.t)
  : Lemma (requires WR.shape_extra r /\ r'.memory.nursery == r.memory.nursery /\ rt_new r r' tag a init /\
                    init_storable r tag init)
          (ensures WR.shape_extra r')
  = if I.tag_scannable tag && Seq.length (young_slots a init) > 0 then begin
      young_slots_index a init 0 0;
      eliminate exists (j: nat). j < Seq.length init /\ is_young (Seq.index init j) /\
                                 Seq.index (young_slots a init) 0 == major_slot a j
      with begin
        assert (storable_value r (Seq.index init j));
        let ms = r.memory.nursery in
        let o = resolve_minor ms (GBase.to_minor_offset (Seq.index init j)) in
        assert (Seq.mem o (minor_objects ms));
        FStar.Seq.Properties.mem_index o (minor_objects ms);
        assert (Seq.length (minor_objects ms) > 0);
        assert (~(minor_objects ms == Seq.empty))
      end
    end
#pop-options

/// The new block's fields, storable for the kept blocks and `a`.
#push-options "--z3rlimit 30"
let init_after (r r': real_state) (h h': cycle_history) (tag: I.tag_t) (init: seq U64.t) (a: obj_addr)
  : Lemma (requires AL.frame r.memory.major r'.memory.major a /\ hist_ok h h' a /\
                    init_storable r tag init /\ D.stores_in_kept r h (Alloc InMajor tag (Seq.length init) init) /\
                    free_def_ok (GI.phase_free r.phase) /\
                    well_formed_heap_with (GI.phase_free r.phase) r.memory.major /\
                    no_infix_block r.memory.major /\ no_infix_block r'.memory.major)
          (ensures I.tag_scannable tag ==>
                     (forall (i: nat). i < Seq.length init ==>
                        SPI.storable (MPC.outside_snapshot (kept h')) r'.memory.major (Seq.index init i)))
  = hist_facts h h' a;
    let one (i: nat)
      : Lemma (I.tag_scannable tag /\ i < Seq.length init ==>
               SPI.storable (MPC.outside_snapshot (kept h')) r'.memory.major (Seq.index init i))
      = if I.tag_scannable tag && i < Seq.length init then begin
          assert (storable_value r (Seq.index init i));
          assert (D.in_kept r h (Seq.index init i));
          storable_after (GI.phase_free r.phase) (kept h) (kept h') r.memory.major r'.memory.major a
            (Seq.index init i)
        end
    in
    FStar.Classical.forall_intro one
#pop-options

/// The new block, as `new_ok` asks.
#push-options "--z3rlimit 30"
let new_after (r r': real_state) (tag: I.tag_t) (size: nat) (init: seq U64.t) (a: obj_addr)
  : Lemma (requires mctx r tag size init r' a /\ blocks_fit r'.memory.major /\
                    (forall (c: U64.t). r.phase == Ph.Sweeping c ==> U64.v c % 8 == 0))
          (ensures new_ok (GI.phase_free r.phase) r'.memory.major a tag init)
  = let g' = r'.memory.major in
    a_in_use g' r.phase a;
    hd_address_spec a;
    assert (U64.v (hd_address a) + 8 + U64.v (wosize_of_object a g') * 8 <= Seq.length g')
#pop-options

/// ---------------------------------------------------------------------------
/// The theorem
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40"
let keeps_with (r: real_state) (h: cycle_history) (tag: I.tag_t) (size: nat) (init: seq U64.t)
               (r': real_state) (a: obj_addr)
  : Lemma (requires D.run_invariant r h /\ D.stores_in_kept r h (Alloc InMajor tag size init) /\
                    mctx r tag size init r' a)
          (ensures D.run_invariant r' (update_history h r (Alloc InMajor tag size init) r'))
  = let h' = update_history h r (Alloc InMajor tag size init) r' in
    let g = r.memory.major in
    let g' = r'.memory.major in
    let ph = r.phase in
    let pf = GI.phase_free ph in
    WR.inv_split r h;
    WR.inv_split r' h';
    a_fresh r tag size init r' a;
    made_a r r' a;
    assert (hist_ok h h' a);
    WR.shape_facts ph r.memory.nursery g r.free_list r.scan_pos;
    WR.shape_facts ph r'.memory.nursery g' r'.free_list r'.scan_pos;
    (match ph with
     | Ph.Sweeping c -> sweep_cursor r.memory.nursery g r.free_list c r.scan_pos
     | _ -> ());
    // the collector's state and the remembered set
    old_ok_intro pf g g' a;
    new_after r r' tag size init a;
    rt_sound pf r r' tag a init;
    rt_covers pf r r' tag a init;
    assert (WR.shape_core r');
    extra_after r r' tag a init;
    // B1
    init_after r r' h h' tag init a;
    hist_facts h h' a;
    within_after (kept h) (kept h') g g' a tag init;
    // B2-B5, the phase
    base_after h h' r.memory r'.memory a;
    phase_after h h' r r' a;
    assert (WR.acc_core r' h');
    rt_kept_after h h' r r' tag a init;
    blk_after h h' r.memory r'.memory ph a
#pop-options

/// **A direct major allocation keeps the run invariant.**
let major_alloc_keeps (r: real_state) (h: cycle_history) (tag: I.tag_t) (size: nat) (init: seq U64.t)
                      (r': real_state)
  : Lemma (requires D.run_invariant r h /\ D.stores_in_kept r h (Alloc InMajor tag size init) /\
                    step r (Alloc InMajor tag size init) r')
          (ensures D.run_invariant r' (update_history h r (Alloc InMajor tag size init) r'))
  = assert (major_alloc_step r tag size init r');
    eliminate exists (a: obj_addr).
      was_free r.memory.major r'.memory.major a /\
      is_allocated r'.memory (Major a) /\
      tag_of_object a r'.memory.major == tag /\ U64.v (wosize_of_object a r'.memory.major) == size /\
      color_of_object a r'.memory.major == Ph.allocation_color r.phase (hd_address a) /\
      (forall (i: nat). i < size ==> block_field r'.memory (Major a) i == Seq.index init i) /\
      (forall (x: obj_addr). x <> a ==>
         (is_allocated r.memory (Major x) <==> is_allocated r'.memory (Major x)) /\
         (is_allocated r.memory (Major x) ==> same_block r.memory.major r'.memory.major x)) /\
      r'.ref_table == (if I.tag_scannable tag then Seq.append r.ref_table (young_slots a init)
                       else r.ref_table)
    with keeps_with r h tag size init r' a
