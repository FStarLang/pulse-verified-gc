/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Promote.Loop - what the Cheney loop keeps, for any allocator
/// ---------------------------------------------------------------------------
///
/// Plan §27.2.  For an allocator that meets `contract`, every state of the
/// loop of `GC.Spec.Pages.Promote` keeps `linv` against the heap `g0` the
/// collection started from:
///
///   * the allocator's invariant;
///   * every block in use in `g0` is in use, with its header and fields;
///   * every other block in use is the copy of a nursery object the
///     forwarding map sends to it (`copy_of`: of its size, tag and fields,
///     in the allocator's colour);
///   * every forwarded nursery object is copied, and an infix one is sent
///     to the same offset in its closure's copy.
///
/// This is what akhil's `GC.Gen.CheneyPreservation.*` and
/// `GC.Gen.Cheney.Steps` prove of his loop from his free list; here it
/// comes from the contract alone.  The step is `step_ok`: one allocation
/// and the copy of the fields.

module GC.Spec.Pages.Promote.Loop

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.WriteBodyLemmas
open GC.Spec.Pages.Promote

module U64 = FStar.UInt64
module I = GC.Spec.AllocIface
module AT = GC.Spec.Pages.AllocTag
module Sh = GC.Spec.Pages.Shape
module F = GC.Spec.Pages.Fill
module GenInv = GC.Gen.HeapInvariant

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The invariant
/// ---------------------------------------------------------------------------

/// What the collection assumes of the nursery.
let mpre (minor: minor_state) : prop = minor_wf minor /\ minor_infix_wf minor

/// What the collection starts from.
let cpre (#s: Type0) (a: tal s) (minor: minor_state) (g0: heap) (st0: s) : prop =
  contract a /\ a.inv g0 st0 /\ mpre minor /\ GenInv.minor_major_fields_not_free a.free minor g0

/// The block of `y` in `g'` is its block in `g`: header and fields.
let kept (g g': heap) (y: obj_addr) : prop =
  read_word g' (hd_address y) == read_word g (hd_address y) /\
  (forall (b: hp_addr). U64.v y <= U64.v b /\ U64.v b < U64.v y + U64.v (wosize_of_object y g) * 8 ==>
     read_word g' b == read_word g b)

/// `v` is a block of `g` in use, not in use in `g0`: the copy of the
/// nursery object `m`, of its size, tag and fields, in the allocator's
/// colour.
let copy_of (#s: Type0) (a: tal s) (minor: minor_state) (g0 g: heap) (m: U64.t) (v: U64.t) : prop =
  Seq.mem m (minor_objects minor) /\ ~(is_infix_in_minor minor m) /\
  U64.v v >= 8 /\ U64.v v < heap_size /\ U64.v v % 8 == 0 /\
  (let x : obj_addr = v in
   in_use a.free g x /\ ~(in_use a.free g0 x) /\
   U64.v x + minor_wosize minor m * 8 <= heap_size /\
   U64.v (wosize_of_object x g) == minor_wosize minor m /\
   tag_of_object x g == promoted_tag minor m /\
   color_of_object x g == a.col /\
   (forall (j: nat). j < minor_wosize minor m ==> Sh.hdr g (U64.v x + j * 8) == minor_read_field minor m j))

/// A forwarding entry: a copy; for an infix address, the same offset in its
/// closure's copy.
let entry (#s: Type0) (a: tal s) (minor: minor_state) (g0 g: heap) (fwd: forwarding_map) (m: U64.t) : prop =
  (~(is_infix_in_minor minor m) ==> copy_of a minor g0 g m (fwd m)) /\
  (is_infix_in_minor minor m ==>
     (let p = infix_parent minor m in
      copy_of a minor g0 g p (fwd p) /\ U64.v m >= U64.v p /\
      U64.v (fwd m) == U64.v (fwd p) + (U64.v m - U64.v p)))

/// The old blocks stay.
let olds (#s: Type0) (a: tal s) (g0 g: heap) : prop =
  forall (y: obj_addr). in_use a.free g0 y ==> in_use a.free g y /\ kept g0 g y

/// The new blocks are copies.
let news (#s: Type0) (a: tal s) (minor: minor_state) (g0 g: heap) (fwd: forwarding_map) : prop =
  forall (y: obj_addr). in_use a.free g y /\ ~(in_use a.free g0 y) ==>
    (exists (m: U64.t). fwd m == (y <: U64.t) /\ copy_of a minor g0 g m (y <: U64.t))

/// The forwarding entries.
let entries (#s: Type0) (a: tal s) (minor: minor_state) (g0 g: heap) (fwd: forwarding_map) : prop =
  forall (m: U64.t). fwd m <> 0UL ==> entry a minor g0 g fwd m

/// **The loop invariant.**
let linv (#s: Type0) (a: tal s) (minor: minor_state) (g0: heap) (cs: gstate s) : prop =
  a.inv cs.major cs.st /\ olds a g0 cs.major /\ news a minor g0 cs.major cs.fwd /\
  entries a minor g0 cs.major cs.fwd

/// ---------------------------------------------------------------------------
/// The step: one allocation, and the copy
/// ---------------------------------------------------------------------------

/// From `g` to `g2` with `x` new: the blocks in use are those before and
/// `x`, and every block in use before keeps its block.
let step_rel (#s: Type0) (a: tal s) (g g2: heap) (x: obj_addr) : prop =
  ~(in_use a.free g x) /\
  (forall (y: obj_addr). in_use a.free g2 y == (in_use a.free g y || y = x)) /\
  (forall (y: obj_addr). in_use a.free g y ==> kept g g2 y)

let kept_trans (g0 g g2: heap) (y: obj_addr)
  : Lemma (requires kept g0 g y /\ kept g g2 y)
          (ensures kept g0 g2 y)
  = wosize_of_object_spec y g0;
    wosize_of_object_spec y g

/// A copy stays a copy across a step that makes another block.
#push-options "--z3rlimit 30"
let copy_frame (#s: Type0) (a: tal s) (minor: minor_state) (g0 g g2: heap) (x: obj_addr) (m v: U64.t)
  : Lemma (requires step_rel a g g2 x /\ copy_of a minor g0 g m v)
          (ensures copy_of a minor g0 g2 m v)
  = let y : obj_addr = v in
    assert (kept g g2 y);
    wosize_of_object_spec y g;
    wosize_of_object_spec y g2;
    tag_of_object_spec y g;
    tag_of_object_spec y g2;
    color_of_object_spec y g;
    color_of_object_spec y g2;
    let fld (j: nat)
      : Lemma (requires j < minor_wosize minor m)
              (ensures Sh.hdr g2 (U64.v y + j * 8) == Sh.hdr g (U64.v y + j * 8))
      = let b = U64.v y + j * 8 in
        if b < heap_size && b % 8 = 0 then assert (read_word g2 (mk_hp_addr b) == read_word g (mk_hp_addr b))
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires fld)
#pop-options

/// The pieces of `linv` across a step whose new block is the copy of
/// `addr`, forwarded to it.
let olds_step (#s: Type0) (a: tal s) (g0 g g2: heap) (x: obj_addr)
  : Lemma (requires olds a g0 g /\ step_rel a g g2 x)
          (ensures olds a g0 g2)
  = let one (y: obj_addr)
      : Lemma (requires in_use a.free g0 y) (ensures in_use a.free g2 y /\ kept g0 g2 y)
      = kept_trans g0 g g2 y
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires one)

#push-options "--z3rlimit 30"
let news_step (#s: Type0) (a: tal s) (minor: minor_state) (g0 g g2: heap) (fwd: forwarding_map)
              (addr: U64.t) (x: obj_addr)
  : Lemma (requires news a minor g0 g fwd /\ step_rel a g g2 x /\ fwd addr == 0UL /\
                    copy_of a minor g0 g2 addr (x <: U64.t))
          (ensures news a minor g0 g2 (extend_forwarding fwd addr (x <: U64.t)))
  = let fwd' = extend_forwarding fwd addr (x <: U64.t) in
    let one (y: obj_addr)
      : Lemma (requires in_use a.free g2 y /\ ~(in_use a.free g0 y))
              (ensures exists (m: U64.t). fwd' m == (y <: U64.t) /\ copy_of a minor g0 g2 m (y <: U64.t))
      = if y = x then assert (fwd' addr == (y <: U64.t))
        else begin
          assert (in_use a.free g y);
          eliminate exists (m: U64.t). fwd m == (y <: U64.t) /\ copy_of a minor g0 g m (y <: U64.t)
          with begin
            copy_frame a minor g0 g g2 x m (y <: U64.t);
            assert (fwd' m == (y <: U64.t))
          end
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires one)
#pop-options

#push-options "--z3rlimit 30"
let entries_step (#s: Type0) (a: tal s) (minor: minor_state) (g0 g g2: heap) (fwd: forwarding_map)
                 (addr: U64.t) (x: obj_addr)
  : Lemma (requires entries a minor g0 g fwd /\ step_rel a g g2 x /\ fwd addr == 0UL /\
                    ~(is_infix_in_minor minor addr) /\
                    copy_of a minor g0 g2 addr (x <: U64.t))
          (ensures entries a minor g0 g2 (extend_forwarding fwd addr (x <: U64.t)))
  = let fwd' = extend_forwarding fwd addr (x <: U64.t) in
    let one (m: U64.t)
      : Lemma (requires fwd' m <> 0UL) (ensures entry a minor g0 g2 fwd' m)
      = if m = addr then ()
        else begin
          assert (entry a minor g0 g fwd m);
          if is_infix_in_minor minor m then begin
            let p = infix_parent minor m in
            assert (copy_of a minor g0 g p (fwd p));
            assert (p <> addr);
            copy_frame a minor g0 g g2 x p (fwd p)
          end else
            copy_frame a minor g0 g g2 x m (fwd m)
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires one)
#pop-options

/// ---------------------------------------------------------------------------
/// One promotion
/// ---------------------------------------------------------------------------

/// The tag a nursery object is copied with is not infix.
let tag_not_infix (minor: minor_state) (addr: U64.t)
  : Lemma (requires mpre minor /\ Seq.mem addr (minor_objects minor))
          (ensures U64.v (promoted_tag minor addr) <> 249 /\ ~(is_infix_in_minor minor addr) /\
                   U64.v (promoted_tag minor addr) == minor_tag minor addr)
  = minor_objects_not_infix minor addr;
    minor_tag_bound minor addr

/// Writing the fields of `x` keeps the blocks in use, and every other
/// block.
#push-options "--z3rlimit 30"
let fill_in_use (free: free_def) (g1 g2: heap) (x: obj_addr) (y: obj_addr)
  : Lemma (requires free_def_ok free /\ F.fctx g1 g2 x)
          (ensures in_use free g2 y == in_use free g1 y /\
                   (Seq.mem y (objects zero_addr g1) ==>
                      read_word g2 (hd_address y) == read_word g1 (hd_address y)))
  = F.obj_same g1 g2 x y;
    if Seq.mem y (objects zero_addr g1) then in_use_is_determined_from_header free g1 g2 y
#pop-options

/// The words the copy writes are the fields of `x`.
let copy_frame_words (minor: minor_state) (g1: heap) (addr: U64.t) (x: obj_addr) (wz: pos) (b: hp_addr)
  : Lemma (requires U64.v x + wz * 8 <= heap_size /\
                    (U64.v b < U64.v x \/ U64.v b >= U64.v x + wz * 8))
          (ensures read_word (copy_fields minor g1 addr x 0 wz) b == read_word g1 b)
  = dst_fields_valid_from_bounds x wz;
    copy_fields_frame minor g1 addr x 0 wz b

/// ... and they hold the nursery object's fields.
#push-options "--z3rlimit 30"
let copy_words (minor: minor_state) (g1: heap) (addr: U64.t) (x: obj_addr) (wz: pos) (j: nat)
  : Lemma (requires U64.v x + wz * 8 <= heap_size /\ j < wz)
          (ensures Sh.hdr (copy_fields minor g1 addr x 0 wz) (U64.v x + j * 8) == minor_read_field minor addr j)
  = dst_fields_valid_from_bounds x wz;
    copy_fields_all_correct minor g1 addr x wz;
    let b = U64.v x + j * 8 in
    FStar.Math.Lemmas.lemma_mod_plus (U64.v x) j 8;
    assert (b < heap_size /\ b % 8 == 0);
    assert (mk_hp_addr b == U64.uint_to_t b)
#pop-options

/// A field written in a scannable copy: a nursery value that is not a major
/// pointer, or a pointer to an old block, in use and away from `x`.
#push-options "--z3rlimit 40"
let copied_field_ok (#s: Type0) (a: tal s) (minor: minor_state) (g0 g g1 g2: heap) (addr: U64.t)
                    (x: obj_addr) (wz: pos) (j: nat)
  : Lemma (requires free_def_ok a.free /\ well_formed_heap_with a.free g0 /\
                    GenInv.minor_major_fields_not_free a.free minor g0 /\
                    Seq.mem addr (minor_objects minor) /\ j < minor_scan_wosize minor addr /\
                    olds a g0 g /\ step_rel a g g2 x /\ Seq.mem x (objects zero_addr g1) /\
                    (forall (y: obj_addr). in_use a.free g1 y ==> Seq.mem y (objects zero_addr g1)) /\
                    U64.v (wosize_of_object x g1) == wz /\
                    (forall (y: obj_addr). Seq.mem y (objects zero_addr g1) /\ y <> x ==>
                       (read_word g2 (hd_address y) == read_word g1 (hd_address y))) /\
                    (forall (y: obj_addr). in_use a.free g y ==> in_use a.free g1 y /\
                       wosize_of_object y g1 == wosize_of_object y g))
          (ensures (let v = minor_read_field minor addr j in
                    I.field_ok_with a.free g2 v /\ AT.away x wz v))
  = let v = minor_read_field minor addr j in
    if is_pointer v then begin
      let w : obj_addr = v in
      GenInv.minor_major_fields_not_free_elim a.free minor g0 addr j;
      // `w` names the block `r` it resolves to: `w` itself, or the closure
      // `w` points into
      let r : obj_addr = resolve_object w g0 in
      assert (in_use a.free g0 r);
      assert (in_use a.free g r /\ kept g0 g r);
      assert (in_use a.free g2 r /\ kept g g2 r);
      kept_trans g0 g g2 r;
      wf_with_parts ();
      free_def_ok_elim a.free;
      // `r` is a block of the walk, with its header: not infix
      assert (~(is_infix r g0));
      resolve_object_locality r g0 g;
      resolve_object_locality r g g2;
      wosize_of_object_spec r g0;
      wosize_of_object_spec r g;
      if is_infix w g0 then begin
        // `w` lies in `r`'s body, and so does its header, which the steps keep
        infix_addr_wf_elim g0 (objects zero_addr g0) w;
        resolve_infix_spec w g0;
        parent_closure_addr_nat_spec w g0;
        hd_address_spec w;
        let wzw = U64.v (wosize_of_object w g0) in
        assert (wzw >= 2 /\ U64.v r == U64.v w - wzw * 8);
        assert (U64.v w < U64.v r + U64.v (wosize_of_object r g0) * 8);
        let hw : hp_addr = hd_address w in
        assert (U64.v hw == U64.v w - 8);
        assert (U64.v r <= U64.v hw /\ U64.v hw < U64.v r + U64.v (wosize_of_object r g0) * 8);
        assert (read_word g2 hw == read_word g0 hw);
        resolve_object_locality w g0 g2;
        infix_addr_wf_transfer g0 g2 (objects zero_addr g0) (objects zero_addr g2) w
      end else begin
        resolve_non_infix w g0;
        resolve_object_locality w g0 g2;
        resolve_non_infix w g2;
        infix_addr_wf_non_infix g2 (objects zero_addr g2) w
      end;
      assert (resolve_object w g2 == r);
      // away from x: `w` lies in `r`'s block, which is apart from `x`
      assert (r <> x);
      F.other_apart g1 x r;
      wosize_of_object_spec r g1
    end
#pop-options

/// A block in use before keeps its block across the allocation and the copy.
#push-options "--z3rlimit 30"
let kept_one (#s: Type0) (a: tal s) (minor: minor_state) (g g1: heap) (addr: U64.t) (x: obj_addr) (wz: pos)
             (y: obj_addr)
  : Lemma (requires free_def_ok a.free /\ I.others_unchanged g g1 /\ in_use a.free g y /\
                    ~(in_use a.free g x) /\ Seq.mem x (objects zero_addr g1) /\
                    U64.v (wosize_of_object x g1) == wz /\ U64.v x + wz * 8 <= heap_size)
          (ensures kept g (copy_fields minor g1 addr x 0 wz) y)
  = let g2 = copy_fields minor g1 addr x 0 wz in
    in_use_not_blue a.free g y;
    assert (Seq.mem y (objects zero_addr g1) /\ read_word g1 (hd_address y) == read_word g (hd_address y));
    assert (y <> x);
    F.other_apart g1 x y;
    wosize_of_object_spec y g1;
    wosize_of_object_spec y g;
    hd_address_spec y;
    copy_frame_words minor g1 addr x wz (hd_address y);
    let body (b: hp_addr)
      : Lemma (requires U64.v y <= U64.v b /\ U64.v b < U64.v y + U64.v (wosize_of_object y g) * 8)
              (ensures read_word g2 b == read_word g b)
      = copy_frame_words minor g1 addr x wz b
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires body)
#pop-options

/// The copy writes the fields of the new block as the allocator asks.
#push-options "--z3rlimit 40"
let written_away (#s: Type0) (a: tal s) (minor: minor_state) (g0 g g1: heap) (addr: U64.t) (x: obj_addr) (wz: pos)
  : Lemma (requires free_def_ok a.free /\ well_formed_heap_with a.free g0 /\
                    GenInv.minor_major_fields_not_free a.free minor g0 /\
                    Seq.mem addr (minor_objects minor) /\ wz == minor_wosize minor addr /\
                    olds a g0 g /\ step_rel a g (copy_fields minor g1 addr x 0 wz) x /\
                    Seq.mem x (objects zero_addr g1) /\ U64.v x + wz * 8 <= heap_size /\
                    U64.v (wosize_of_object x g1) == wz /\
                    tag_of_object x g1 == promoted_tag minor addr /\
                    U64.v (promoted_tag minor addr) == minor_tag minor addr /\
                    F.fctx g1 (copy_fields minor g1 addr x 0 wz) x /\
                    (forall (y: obj_addr). in_use a.free g y ==> in_use a.free g1 y /\
                       wosize_of_object y g1 == wosize_of_object y g))
          (ensures AT.fields_written_away a.free g1 (copy_fields minor g1 addr x 0 wz) x)
  = let g2 = copy_fields minor g1 addr x 0 wz in
    free_def_ok_elim a.free;
    FStar.Classical.forall_intro (fill_in_use a.free g1 g2 x);
    FStar.Classical.forall_intro (FStar.Classical.move_requires (copy_frame_words minor g1 addr x wz));
    if not (is_no_scan x g1) then begin
      is_no_scan_spec x g1;
      no_scan_tag_val ();
      minor_scan_wosize_cases minor addr;
      assert (minor_scan_wosize minor addr == wz);
      let body (b: hp_addr)
        : Lemma (requires U64.v x <= U64.v b /\ U64.v b < U64.v x + wz * 8)
                (ensures I.field_ok_with a.free g2 (read_word g2 b) /\ AT.away x wz (read_word g2 b))
        = let j = (U64.v b - U64.v x) / 8 in
          FStar.Math.Lemmas.lemma_div_exact (U64.v b - U64.v x) 8;
          assert (U64.v x + j * 8 == U64.v b);
          copy_words minor g1 addr x wz j;
          assert (mk_hp_addr (U64.v b) == b);
          copied_field_ok a minor g0 g g1 g2 addr x wz j
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires body)
    end
#pop-options

/// **One promotion**, from a state of the loop: on failure nothing changes;
/// on success the allocator's invariant holds, the step makes one block,
/// the copy of `addr`, and keeps every other block in use.
#push-options "--z3rlimit 40"
let promote_step (#s: Type0) (a: tal s) (minor: minor_state) (g0 g: heap) (st: s) (addr: U64.t)
  : Lemma (requires contract a /\ mpre minor /\ GenInv.minor_major_fields_not_free a.free minor g0 /\
                    well_formed_heap_with a.free g0 /\ a.inv g st /\ olds a g0 g /\
                    Seq.mem addr (minor_objects minor) /\ minor_wosize minor addr > 0)
          (ensures (let (g2, s2, o) = promote_object a minor g addr st (minor_wosize minor addr) in
                    (o == 0UL ==> g2 == g /\ s2 == st) /\
                    (o =!= 0UL ==>
                       U64.v o >= 8 /\ U64.v o < heap_size /\ U64.v o % 8 == 0 /\
                       a.inv g2 s2 /\ step_rel a g g2 (o <: obj_addr) /\ copy_of a minor g0 g2 addr o)))
  = let wz : pos = minor_wosize minor addr in
    let tag = promoted_tag minor addr in
    tag_not_infix minor addr;
    contract_alloc a g st wz tag;
    let (g1, s1, o) = a.alloc g st wz tag in
    if o = 0UL then ()
    else begin
      let x : obj_addr = o in
      let g2 = copy_fields minor g1 addr x 0 wz in
      free_def_ok_elim a.free;
      FStar.Classical.forall_intro (FStar.Classical.move_requires (copy_frame_words minor g1 addr x wz));
      assert (F.fctx g1 g2 x);
      FStar.Classical.forall_intro (fill_in_use a.free g1 g2 x);
      FStar.Classical.forall_intro (FStar.Classical.move_requires (kept_one a minor g g1 addr x wz));
      assert (step_rel a g g2 x);
      let sz (y: obj_addr)
        : Lemma (requires in_use a.free g y)
                (ensures in_use a.free g1 y /\ wosize_of_object y g1 == wosize_of_object y g)
        = in_use_not_blue a.free g y;
          wosize_of_object_spec y g1;
          wosize_of_object_spec y g
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires sz);
      written_away a minor g0 g g1 addr x wz;
      assert (a.inv g2 s1);
      // the copy
      wosize_of_object_spec x g1; wosize_of_object_spec x g2;
      tag_of_object_spec x g1; tag_of_object_spec x g2;
      color_of_object_spec x g1; color_of_object_spec x g2;
      FStar.Classical.forall_intro (FStar.Classical.move_requires (copy_words minor g1 addr x wz));
      assert (~(in_use a.free g0 x))
    end
#pop-options

/// ---------------------------------------------------------------------------
/// The loop keeps the invariant
/// ---------------------------------------------------------------------------

/// What holds throughout a collection from `g0`.
let ctx (#s: Type0) (a: tal s) (minor: minor_state) (g0: heap) : prop =
  contract a /\ mpre minor /\ GenInv.minor_major_fields_not_free a.free minor g0 /\
  well_formed_heap_with a.free g0

let forward_normal_keeps (#s: Type0) (a: tal s) (minor: minor_state) (g0: heap) (cs: gstate s) (addr: U64.t)
  : Lemma (requires ctx a minor g0 /\ linv a minor g0 cs)
          (ensures linv a minor g0 (forward_normal a minor cs addr) /\
                   (forall (m: U64.t). m <> addr ==> (forward_normal a minor cs addr).fwd m == cs.fwd m))
  = if not (Seq.mem addr (minor_objects minor)) || cs.fwd addr <> 0UL then ()
    else begin
      let wz = minor_wosize minor addr in
      if wz = 0 then ()
      else begin
        promote_step a minor g0 cs.major cs.st addr;
        let (g2, s2, o) = promote_object a minor cs.major addr cs.st wz in
        if o = 0UL then ()
        else begin
          let x : obj_addr = o in
          tag_not_infix minor addr;
          olds_step a g0 cs.major g2 x;
          news_step a minor g0 cs.major g2 cs.fwd addr x;
          entries_step a minor g0 cs.major g2 cs.fwd addr x
        end
      end
    end

/// The parent of an infix nursery address is a nursery object, not infix.
let parent_facts (minor: minor_state) (addr: U64.t)
  : Lemma (requires mpre minor /\ is_infix_in_minor minor addr)
          (ensures (let p = infix_parent minor addr in
                    Seq.mem p (minor_objects minor) /\ ~(is_infix_in_minor minor p) /\ p <> addr))
  = infix_parent_in_minor_objects minor addr;
    tag_not_infix minor (infix_parent minor addr)

/// An infix address forwarded to the same offset in its closure's copy.
#push-options "--z3rlimit 30"
let infix_step (#s: Type0) (a: tal s) (minor: minor_state) (g0 g: heap) (fwd: forwarding_map) (addr: U64.t)
               (v: U64.t)
  : Lemma (requires mpre minor /\ news a minor g0 g fwd /\ entries a minor g0 g fwd /\
                    is_infix_in_minor minor addr /\
                    (let p = infix_parent minor addr in
                     fwd p <> 0UL /\ U64.v addr >= U64.v p /\
                     U64.v v == U64.v (fwd p) + (U64.v addr - U64.v p)))
          (ensures news a minor g0 g (extend_forwarding fwd addr v) /\
                   entries a minor g0 g (extend_forwarding fwd addr v))
  = let fwd' = extend_forwarding fwd addr v in
    parent_facts minor addr;
    let nw (y: obj_addr)
      : Lemma (requires in_use a.free g y /\ ~(in_use a.free g0 y))
              (ensures exists (m: U64.t). fwd' m == (y <: U64.t) /\ copy_of a minor g0 g m (y <: U64.t))
      = eliminate exists (m: U64.t). fwd m == (y <: U64.t) /\ copy_of a minor g0 g m (y <: U64.t)
        with assert (fwd' m == (y <: U64.t))
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires nw);
    let en (m: U64.t)
      : Lemma (requires fwd' m <> 0UL) (ensures entry a minor g0 g fwd' m)
      = if m = addr then assert (entry a minor g0 g fwd (infix_parent minor addr))
        else begin
          assert (entry a minor g0 g fwd m);
          if is_infix_in_minor minor m then parent_facts minor m
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires en)
#pop-options

#push-options "--z3rlimit 30"
let forward_one_keeps (#s: Type0) (a: tal s) (minor: minor_state) (g0: heap) (cs: gstate s) (addr: U64.t)
  : Lemma (requires ctx a minor g0 /\ linv a minor g0 cs)
          (ensures linv a minor g0 (forward_one a minor cs addr))
  = if cs.fwd addr <> 0UL then ()
    else if is_infix_in_minor minor addr then begin
      let parent = infix_parent minor addr in
      parent_facts minor addr;
      forward_normal_keeps a minor g0 cs parent;
      let cs' = forward_normal a minor cs parent in
      if cs'.fwd parent <> 0UL &&
         U64.v addr >= U64.v parent &&
         U64.v (cs'.fwd parent) + (U64.v addr - U64.v parent) < heap_size
      then begin
        let v = U64.uint_to_t (U64.v (cs'.fwd parent) + (U64.v addr - U64.v parent)) in
        infix_step a minor g0 cs'.major cs'.fwd addr v
      end
    end
    else forward_normal_keeps a minor g0 cs addr
#pop-options

#push-options "--fuel 1 --ifuel 0"
let rec forward_fields_keeps (#s: Type0) (a: tal s) (minor: minor_state) (g0: heap) (cs: gstate s)
                             (parent: U64.t) (idx: nat) (wz: nat)
  : Lemma (requires ctx a minor g0 /\ linv a minor g0 cs)
          (ensures linv a minor g0 (forward_fields a minor cs parent idx wz))
          (decreases (if idx >= wz then 0 else wz - idx))
  = if idx >= wz then ()
    else begin
      let fv = to_minor_offset (minor_read_field minor parent idx) in
      forward_one_keeps a minor g0 cs fv;
      forward_fields_keeps a minor g0 (forward_one a minor cs fv) parent (idx + 1) wz
    end

let rec forward_roots_keeps (#s: Type0) (a: tal s) (minor: minor_state) (g0: heap) (cs: gstate s)
                            (roots: seq U64.t) (idx: nat)
  : Lemma (requires ctx a minor g0 /\ linv a minor g0 cs)
          (ensures linv a minor g0 (forward_roots a minor cs roots idx))
          (decreases (if idx >= Seq.length roots then 0 else Seq.length roots - idx))
  = if idx >= Seq.length roots then ()
    else begin
      forward_one_keeps a minor g0 cs (Seq.index roots idx);
      forward_roots_keeps a minor g0 (forward_one a minor cs (Seq.index roots idx)) roots (idx + 1)
    end

let rec scan_keeps (#s: Type0) (a: tal s) (minor: minor_state) (g0: heap) (cs: gstate s) (sc: nat) (fuel: nat)
  : Lemma (requires ctx a minor g0 /\ linv a minor g0 cs)
          (ensures linv a minor g0 (scan a minor cs sc fuel))
          (decreases fuel)
  = if fuel = 0 then ()
    else if sc >= Seq.length cs.queue then ()
    else begin
      let fuel' : nat = fuel - 1 in
      let obj = Seq.index cs.queue sc in
      let cs' = forward_fields a minor cs obj 0 (minor_scan_wosize minor obj) in
      forward_fields_keeps a minor g0 cs obj 0 (minor_scan_wosize minor obj);
      assert (scan a minor cs sc fuel == scan a minor cs' (sc + 1) fuel');
      scan_keeps a minor g0 cs' (sc + 1) fuel'
    end
#pop-options

/// **Promotion keeps the invariant**: from the heap `g0` in the allocator's
/// invariant, the loop ends in a state of `linv`.
let promote_linv (#s: Type0) (a: tal s) (minor: minor_state) (g0: heap) (st0: s) (roots: seq U64.t)
  : Lemma (requires cpre a minor g0 st0)
          (ensures ctx a minor g0 /\ linv a minor g0 (promote a minor g0 st0 roots))
  = contract_wf a g0 st0;
    let cs0 : gstate s = { major = g0; st = st0; fwd = empty_forwarding; queue = Seq.empty } in
    assert (olds a g0 g0);
    assert (linv a minor g0 cs0);
    forward_roots_keeps a minor g0 cs0 roots 0;
    let cs1 = forward_roots a minor cs0 roots 0 in
    scan_keeps a minor g0 cs1 0 (Seq.length (minor_objects minor))
