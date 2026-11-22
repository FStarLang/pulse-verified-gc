/// ---------------------------------------------------------------------------
/// GC.Spec.Top.FFFill - the first-fit invariant after the Fill of a new block
/// ---------------------------------------------------------------------------
///
/// Design doc §13.  A first-fit allocation hands out a block whose fields
/// still hold what the free block held (a list link, say), so the heap is
/// well formed only once the caller has written them.  akhil states this as
/// "fresh" objects, counted free until closed (`SweepPhase.Mutator.fresh_ok`,
/// `fresh_close`; `MarkPhase.Alloc.marking_fresh`, which needs the marking
/// invariant).  Here, for any change that writes only the new block's body
/// with storable values (`AT.fields_written_away`):
///   - `transport`: the walk and every header stay, and every other block's
///     body, so well-formedness with the new block counted free carries over;
///   - `close`: once the fields are storable, the heap is well formed;
///   - `marking_fill`: the colour-blind shape of the marking phase holds after
///     an allocation and the Fill (no marking invariant needed);
///   - `sweep_fill`: akhil's sweep invariant holds after an allocation at a
///     sweep's phase and the Fill.

module GC.Spec.Top.FFFill

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Spec.Top.FFAlloc
module U64 = FStar.UInt64
module Seq = FStar.Seq
module W = GC.Spec.Walk
module Ph = GC.Spec.Phase
module SA = GC.Spec.Allocator
module AP = GC.Spec.Allocator.Phase
module AC = GC.Spec.Allocator.Cursor
module FL = GC.Spec.FreeList
module FLA = GC.Spec.FreeList.Ascending
module SPI = GC.Spec.SweepPhase.Intrinsic
module Mut = GC.Spec.SweepPhase.Mutator
module MA = GC.Spec.MarkPhase.Alloc
module FT = GC.Spec.FieldTarget
module AT = GC.Spec.Pages.AllocTag
module I = GC.Spec.AllocIface
module FB = GC.Spec.Top.FFBytes

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Writing a block's body
/// ---------------------------------------------------------------------------

/// The walk does not stop inside the fields of an object.
let walk_apart (g: heap) (x: obj_addr) (q: hp_addr)
  : Lemma (requires Seq.mem x (objects zero_addr g) /\ W.reaches g zero_addr (U64.v q))
          (ensures U64.v q < U64.v x \/ U64.v q >= U64.v x + 8 * U64.v (wosize_of_object x g))
  = W.objects_mem_iff g zero_addr x;
    hd_address_spec x;
    if U64.v q >= U64.v x then begin
      W.reaches_block_before g zero_addr (hd_address x) (U64.v q);
      wosize_of_object_spec x g
    end

/// `g''` is `g'` but for words of `x`'s body.
let body_only (g' g'': heap) (x: obj_addr) : prop =
  forall (a: hp_addr).
    U64.v a < U64.v x \/ U64.v a >= U64.v x + U64.v (wosize_of_object x g') * 8 ==>
    read_word g'' a == read_word g' a

/// Writing only `x`'s body keeps the walk and every header.
#push-options "--z3rlimit 40"
let body_heads (g' g'': heap) (x: obj_addr)
  : Lemma (requires body_only g' g'' x /\ Seq.mem x (objects zero_addr g'))
          (ensures SPI.same_heads g' g'')
  = let hd (q: hp_addr)
      : Lemma (W.reaches g' zero_addr (U64.v q) ==> getWosize (read_word g'' q) == getWosize (read_word g' q) /\
                                                    read_word g'' q == read_word g' q)
      = if W.reaches g' zero_addr (U64.v q) then begin
          walk_apart g' x q;
          wosize_of_object_spec x g'
        end in
    FStar.Classical.forall_intro hd;
    W.walk_congr g' g'' zero_addr
#pop-options

/// ... and every other object's block.
#push-options "--z3rlimit 40"
let body_other (g' g'': heap) (x y: obj_addr)
  : Lemma (requires body_only g' g'' x /\ Seq.mem x (objects zero_addr g') /\
                    Seq.mem y (objects zero_addr g') /\ y <> x)
          (ensures SPI.same_block g' g'' (hd_address y))
  = body_heads g' g'' x;
    SPI.same_heads_facts g' g'';
    SPI.obj_pos g' y;
    let b (a: hp_addr)
      : Lemma (requires U64.v (hd_address y) < U64.v a /\ U64.v a < W.bnext g' (hd_address y))
              (ensures read_word g'' a == read_word g' a)
      = if U64.v x <= U64.v a && U64.v a < U64.v x + U64.v (wosize_of_object x g') * 8 then
          Mut.other_body g' x y a
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires b);
    hd_address_spec y;
    SPI.colour_of g' y
#pop-options

/// **Transport**: for a definition of free counting `x` free, writing `x`'s
/// body keeps well-formedness.
#push-options "--z3rlimit 40"
let transport (free: free_def) (g' g'': heap) (x: obj_addr)
  : Lemma (requires body_only g' g'' x /\ Seq.mem x (objects zero_addr g') /\ free_def_ok free /\
                    ~(in_use free g' x) /\ well_formed_heap_with free g')
          (ensures well_formed_heap_with free g'' /\ SPI.same_heads g' g'' /\
                   (forall (y: obj_addr). in_use free g'' y == in_use free g' y))
  = body_heads g' g'' x;
    SPI.same_heads_facts g' g'';
    wf_with_parts ();
    Mut.same_heads_part4 g' g'';
    free_def_ok_elim free;
    let sb (y: obj_addr)
      : Lemma (requires in_use free g' y) (ensures SPI.same_block g' g'' (hd_address y))
      = body_other g' g'' x y in
    FStar.Classical.forall_intro (FStar.Classical.move_requires sb);
    SPI.wf_transport g' g'' free free
#pop-options

/// **Close**: once `x`'s fields are storable for `free`, the heap is well
/// formed for `free`, from well-formedness counting `x` free too.
#push-options "--z3rlimit 40"
let close (free fresh: free_def) (g: heap) (x: obj_addr)
  : Lemma (requires free_def_ok free /\ free_def_ok fresh /\ blocks_fit g /\ no_infix_block g /\
                    well_formed_heap_with fresh g /\
                    (forall (y: obj_addr). in_use free g y ==> in_use fresh g y \/ y == x) /\
                    (forall (y: obj_addr). in_use fresh g y ==> in_use free g y) /\
                    (~(is_no_scan x g) ==>
                       (forall (a: hp_addr). U64.v x <= U64.v a /\ U64.v a < U64.v x + U64.v (wosize_of_object x g) * 8 ==>
                          I.field_ok_with free g (read_word g a))))
          (ensures well_formed_heap_with free g)
  = wf_with_parts ();
    free_def_ok_elim free;
    free_def_ok_elim fresh;
    let closure (src: obj_addr) (j: nat)
      : Lemma (requires in_use free g src /\ ~(is_no_scan src g) /\
                        j < U64.v (wosize_of_object src g) /\ U64.v src + j * 8 + 8 <= heap_size)
              (ensures (let w = read_word g (U64.uint_to_t (U64.v src + j * 8)) in
                        is_pointer w ==>
                        in_use free g (resolve_object (w <: obj_addr) g) /\
                        infix_addr_wf g (objects zero_addr g) (w <: obj_addr)))
      = let w = read_word g (U64.uint_to_t (U64.v src + j * 8)) in
        FStar.Math.Lemmas.lemma_mod_plus (U64.v src) j 8;
        if src = x then ()
        else if is_pointer w then FT.wf_with_field fresh g src j
    in
    pointer_clauses_from_field_closure free g closure
#pop-options

/// ---------------------------------------------------------------------------
/// What carries over the Fill
/// ---------------------------------------------------------------------------

/// The free list: the cells and their links stay.
#push-options "--z3rlimit 40"
let fl_after (g' g'': heap) (fp: U64.t) (x: obj_addr)
  : Lemma (requires FLA.fl_ascending g' fp /\ body_only g' g'' x /\ Seq.mem x (objects zero_addr g') /\
                    ~(is_blue x g'))
          (ensures FLA.fl_ascending g'' fp)
  = body_heads g' g'' x;
    SPI.same_heads_facts g' g'';
    let lk (c: U64.t) : Lemma (FL.fl_cell g' c ==> FL.fl_next g'' c == FL.fl_next g' c)
      = if FStar.IndefiniteDescription.strong_excluded_middle (FL.fl_cell g' c) then begin
          let y : obj_addr = c in
          assert (Seq.mem y (objects zero_addr g') /\ is_blue y g' /\ U64.v (wosize_of_object y g') >= 1);
          assert (y <> x);
          body_other g' g'' x y;
          SPI.obj_pos g' y;
          SPI.colour_of g' y;
          hd_address_spec y;
          assert (U64.v (hd_address y) < U64.v (y <: hp_addr) /\ U64.v (y <: hp_addr) < W.bnext g' (hd_address y))
        end in
    FStar.Classical.forall_intro lk;
    FLA.fl_ascending_transfer g' g'' fp
#pop-options

/// The walk to the end, and density.
let walk_after (g' g'': heap)
  : Lemma (requires SPI.same_heads g' g'' /\ W.reaches g' zero_addr heap_size /\
                    heap_objects_dense g' /\ Seq.length (objects zero_addr g') > 0)
          (ensures W.reaches g'' zero_addr heap_size /\ heap_objects_dense g'' /\
                   Seq.length (objects zero_addr g'') > 0)
  = W.reaches_end_of_dense g';
    W.reaches_refl g' zero_addr;
    assert (read_word g'' zero_addr == read_word g' zero_addr);
    SPI.same_heads_facts g' g'';
    W.dense_of_reaches_end g'' heap_size

/// A block kept with its header and body keeps its block.
let kept_block (g g': heap) (y: obj_addr)
  : Lemma (requires Seq.mem y (objects zero_addr g) /\ read_word g' (hd_address y) == read_word g (hd_address y) /\
                    (forall (b: hp_addr). U64.v y <= U64.v b /\ U64.v b < U64.v y + U64.v (wosize_of_object y g) * 8 ==>
                       read_word g' b == read_word g b))
          (ensures SPI.same_block g g' (hd_address y))
  = SPI.obj_pos g y;
    SPI.colour_of g y;
    hd_address_spec y

/// Every block in use has a field, across a change keeping the walk and
/// the headers.
let nz_heads (g g': heap)
  : Lemma (requires SPI.same_heads g g' /\ nz g) (ensures nz g')
  = SPI.same_heads_facts g g';
    let one (x: obj_addr)
      : Lemma (Seq.mem x (objects zero_addr g') /\ ~(is_blue x g') ==> U64.v (wosize_of_object x g') >= 1)
      = if Seq.mem x (objects zero_addr g') then begin
          hd_address_spec x;
          wosize_of_object_spec x g; wosize_of_object_spec x g';
          color_of_object_spec x g; color_of_object_spec x g';
          is_blue_iff x g; is_blue_iff x g'
        end in
    FStar.Classical.forall_intro one

/// ... and across an allocation of a block with a field.
let nz_alloc (ph: Ph.gc_phase) (g: heap) (wz: nat) (tag: AP.tag_t) (g': heap) (x: obj_addr)
  : Lemma (requires nz g /\ FB.new_ok ph g wz tag g' x /\ wz >= 1) (ensures nz g')
  = let one (y: obj_addr)
      : Lemma (Seq.mem y (objects zero_addr g') /\ ~(is_blue y g') ==> U64.v (wosize_of_object y g') >= 1)
      = if Seq.mem y (objects zero_addr g') && not (is_blue y g') && y <> x then begin
          assert (in_use free_stw g' y);
          assert (in_use free_stw g y);
          hd_address_spec y;
          wosize_of_object_spec y g; wosize_of_object_spec y g'
        end in
    FStar.Classical.forall_intro one

/// ---------------------------------------------------------------------------
/// Marking: the colour-blind shape after the allocation and the Fill
/// ---------------------------------------------------------------------------

/// Right after the allocation, the heap is well formed with the new block
/// counted free.
#push-options "--z3rlimit 40"
let fresh_after (ph: Ph.gc_phase) (g: heap) (fp: U64.t) (wz: nat) (tag: AP.tag_t) (x: obj_addr)
  : Lemma (requires FB.ready g fp /\ well_formed_heap g /\ wz >= 1 /\ U64.v tag <> 249 /\
                    (AP.alloc_at ph g fp wz tag).SA.obj_out == (x <: U64.t))
          (ensures (let r = AP.alloc_at ph g fp wz tag in
                    well_formed_heap_with (MA.free_or_new x) r.SA.heap_out /\
                    (forall (y: obj_addr). in_use (MA.free_or_new x) r.SA.heap_out y == in_use free_stw g y)))
  = FB.alloc_bytes ph g fp wz tag;
    let r = AP.alloc_at ph g fp wz tag in
    let g' = r.SA.heap_out in
    MA.free_or_new_ok x;
    free_stw_ok ();
    free_def_ok_elim free_stw;
    let iu (y: obj_addr) : Lemma (in_use (MA.free_or_new x) g' y == in_use free_stw g y)
      = assert (in_use free_stw g' y == (in_use free_stw g y || y = x)) in
    FStar.Classical.forall_intro iu;
    let sb (y: obj_addr) : Lemma (requires in_use free_stw g y) (ensures SPI.same_block g g' (hd_address y))
      = kept_block g g' y in
    FStar.Classical.forall_intro (FStar.Classical.move_requires sb);
    SPI.wf_transport g g' free_stw (MA.free_or_new x)
#pop-options

/// **While marking**, the shape holds after the allocation and the Fill.
#push-options "--z3rlimit 40"
let marking_fill (ph: Ph.gc_phase) (g: heap) (fp: U64.t) (wz: nat) (tag: AP.tag_t) (x: obj_addr) (g'': heap)
  : Lemma (requires mshape g fp /\ wz >= 1 /\ U64.v tag <> 249 /\
                    (AP.alloc_at ph g fp wz tag).SA.obj_out == (x <: U64.t) /\
                    AT.fields_written_away free_stw (AP.alloc_at ph g fp wz tag).SA.heap_out g'' x)
          (ensures mshape g'' (AP.alloc_at ph g fp wz tag).SA.fp_out)
  = reveal_opaque (`%mshape) (mshape g fp);
    wf_with_parts ();
    FB.alloc_bytes ph g fp wz tag;
    let r = AP.alloc_at ph g fp wz tag in
    let g' = r.SA.heap_out in
    fresh_after ph g fp wz tag x;
    MA.free_or_new_ok x;
    free_stw_ok ();
    transport (MA.free_or_new x) g' g'' x;
    SPI.same_heads_facts g' g'';
    Mut.same_heads_part4 g' g'';
    walk_after g' g'';
    free_def_ok_elim free_stw;
    free_def_ok_elim (MA.free_or_new x);
    hd_address_spec x;
    wosize_of_object_spec x g'; wosize_of_object_spec x g'';
    is_no_scan_spec x g'; is_no_scan_spec x g'';
    tag_of_object_spec x g'; tag_of_object_spec x g'';
    assert (wosize_of_object x g'' == wosize_of_object x g');
    assert (is_no_scan x g'' == is_no_scan x g');
    let iu (y: obj_addr) : Lemma (in_use free_stw g'' y == (in_use (MA.free_or_new x) g'' y || y = x))
      = SPI.colour_of g' x in
    FStar.Classical.forall_intro iu;
    close free_stw (MA.free_or_new x) g'' x;
    SPI.colour_of g' x;
    fl_after g' g'' r.SA.fp_out x;
    nz_alloc ph g wz tag g' x;
    nz_heads g' g'';
    reveal_opaque (`%mshape) (mshape g'' r.SA.fp_out)
#pop-options

/// ---------------------------------------------------------------------------
/// Mid-sweep: akhil's invariant after the allocation and the Fill
/// ---------------------------------------------------------------------------

/// The Fill's fields are akhil's storable fields.
#push-options "--z3rlimit 40"
let storable_of (free: free_def) (g' g'': heap) (x: obj_addr)
  : Lemma (requires AT.fields_written_away free g' g'' x /\ Seq.mem x (objects zero_addr g') /\
                    read_word g'' (hd_address x) == read_word g' (hd_address x))
          (ensures Mut.fields_storable free g'' x)
  = hd_address_spec x;
    wosize_of_object_spec x g'; wosize_of_object_spec x g'';
    is_no_scan_spec x g'; is_no_scan_spec x g'';
    tag_of_object_spec x g'; tag_of_object_spec x g'';
    assert (wosize_of_object x g'' == wosize_of_object x g' /\ is_no_scan x g'' == is_no_scan x g');
    if not (is_no_scan x g'') then begin
      let one (i: nat)
        : Lemma (i < U64.v (wosize_of_object x g'') /\ U64.v x + i * 8 + 8 <= heap_size ==>
                 SPI.storable free g'' (Mut.field_val g'' x i))
        = if i < U64.v (wosize_of_object x g'') && U64.v x + i * 8 + 8 <= heap_size then begin
            FStar.Math.Lemmas.lemma_mod_plus (U64.v x) i 8;
            let a : hp_addr = U64.uint_to_t (U64.v x + i * 8) in
            assert (U64.v x <= U64.v a /\ U64.v a < U64.v x + U64.v (wosize_of_object x g') * 8);
            assert (I.field_ok_with free g'' (read_word g'' a));
            assert (Mut.field_val g'' x i == read_word g'' a)
          end in
      FStar.Classical.forall_intro one
    end
#pop-options

/// The sweep invariant gives what an allocation needs.
let ready_of_sweep (g: heap) (fp: U64.t) (c: U64.t)
  : Lemma (requires SPI.sweep_inv_incremental g fp c /\ W.reaches g zero_addr heap_size)
          (ensures FB.ready g fp)
  = SPI.sweep_inv_incremental_elim g fp c;
    wf_with_parts ()

/// **Mid-sweep at `c`**, akhil's invariant holds after the allocation and
/// the Fill.
#push-options "--z3rlimit 40"
let sweep_fill (c: U64.t) (g: heap) (fp: U64.t) (wz: nat) (tag: AP.tag_t) (x: obj_addr) (g'': heap)
  : Lemma (requires SPI.sweep_inv_incremental g fp c /\ W.reaches g zero_addr heap_size /\ nz g /\
                    wz >= 1 /\ U64.v tag <> 249 /\
                    (AP.alloc_at (Ph.Sweeping c) g fp wz tag).SA.obj_out == (x <: U64.t) /\
                    AT.fields_written_away (SPI.free_incremental c) (AP.alloc_at (Ph.Sweeping c) g fp wz tag).SA.heap_out g'' x)
          (ensures SPI.sweep_inv_incremental g'' (AP.alloc_at (Ph.Sweeping c) g fp wz tag).SA.fp_out c /\
                   W.reaches g'' zero_addr heap_size /\ nz g'')
  = infix_tag_val ();
    ready_of_sweep g fp c;
    FB.alloc_bytes (Ph.Sweeping c) g fp wz tag;
    Mut.alloc_sweep_phase g fp c wz tag;
    let r = AP.alloc_at (Ph.Sweeping c) g fp wz tag in
    let g' = r.SA.heap_out in
    let fp' = r.SA.fp_out in
    let fresh = Mut.free_or_uninitialised c x in
    Mut.free_or_uninitialised_ok c x;
    SPI.free_incremental_ok c;
    transport fresh g' g'' x;
    SPI.same_heads_facts g' g'';
    SPI.sweep_shape_elim g' fp' c;
    fl_after g' g'' fp' x;
    SPI.shape_transport g' g'' fp' c;
    hd_address_spec x;
    storable_of (SPI.free_incremental c) g' g'' x;
    assert (Mut.fresh_ok g'' fp' c x);
    Mut.fresh_close g'' fp' c x;
    walk_after g' g'';
    nz_alloc (Ph.Sweeping c) g wz tag g' x;
    nz_heads g' g''
#pop-options
