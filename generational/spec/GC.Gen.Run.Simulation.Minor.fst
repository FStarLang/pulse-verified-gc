module GC.Gen.Run.Simulation.Minor

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.MinorHeap
open GC.Gen.Run.Step
open GC.Gen.Run.History
open GC.Gen.Run.Invariant
open GC.Model.Represents

module U64 = FStar.UInt64
module Ph = GC.Spec.Phase
module I = GC.Model.Ideal
module GBase = GC.Gen.Base
module GI = GC.Gen.Incremental
module GenInv = GC.Gen.HeapInvariant
module Promote = GC.Gen.Promote
module Cheney = GC.Gen.Cheney
module CG = GC.Gen.CheneyGeneric
module BFS = GC.Gen.CheneyBFS
module Fwd = GC.Gen.CheneyPreservation.Forwarding
module Inj = GC.Gen.CheneyPreservation.Injectivity
module CPF = GC.Gen.CheneyPreservation.Fields
module PU = GC.Gen.PromoteUpdate
module MCFH = GC.Gen.MinorCollectForwarding.Helpers
module RT = GC.Gen.RefTable
module Reach = GC.Gen.Reachability
module NA = GC.Gen.Run.NurseryAddr
module SPI = GC.Spec.SweepPhase.Intrinsic

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10"

/// ---------------------------------------------------------------------------
/// The collection's parts
/// ---------------------------------------------------------------------------

let free_of (r: real_state) : free_def = GI.phase_free r.phase
let rs_of (r: real_state) (roots: seq U64.t) : GTot (seq U64.t) = collector_roots r roots
let prom_of (r: real_state) (roots: seq U64.t) : GTot Promote.promote_all_result =
  Cheney.cheney_promote r.phase r.memory.nursery r.memory.major r.free_list (rs_of r roots)
let fwd_of (r: real_state) (roots: seq U64.t) : Promote.forwarding_map = (prom_of r roots).Promote.fwd_map
let gp_of (r: real_state) (roots: seq U64.t) : GTot heap = (prom_of r roots).Promote.major_final

/// What the proofs below use of the state before the collection.
[@@"opaque_to_smt"]
let mctx (r: real_state) (roots: seq U64.t) : prop =
  let ms = r.memory.nursery in
  let g = r.memory.major in
  let fp = r.free_list in
  let free = free_of r in
  let fwd = fwd_of r roots in
  let gp = gp_of r roots in
  CG.promote_pre ms g fp /\
  free_def_ok free /\ free_def_ok free_stw /\
  Promote.allocations_not_free r.phase free /\ Promote.allocations_not_free r.phase free_stw /\
  well_formed_heap_with free g /\ well_formed_heap_with free gp /\ blocks_fit gp /\ no_infix_block gp /\
  (forall (x: obj_addr). in_use free g x ==> Seq.mem x (objects zero_addr g) /\ ~(is_blue x g)) /\
  BFS.fwd_well_formed ms fwd (rs_of r roots) /\
  Fwd.fwd_infix_delta ms fwd /\
  Inj.fwd_normal_injective fwd gp /\
  Fwd.fwd_noninfix_targets_valid ms fwd gp /\
  Inj.fwd_normal_targets_disjoint_from_old_nonblue fwd gp g /\
  RT.ref_table_covers_with free g r.ref_table (Seq.length r.ref_table) /\
  MCFH.roots_valid_for_minor_collection ms g (rs_of r roots) /\
  nursery_fields_valid ms

let mctx_elim (r: real_state) (roots: seq U64.t)
  : Lemma (requires mctx r roots)
          (ensures (let ms = r.memory.nursery in
                    let g = r.memory.major in
                    let fp = r.free_list in
                    let free = free_of r in
                    let fwd = fwd_of r roots in
                    let gp = gp_of r roots in
                    CG.promote_pre ms g fp /\
                    free_def_ok free /\ free_def_ok free_stw /\
                    Promote.allocations_not_free r.phase free /\ Promote.allocations_not_free r.phase free_stw /\
                    well_formed_heap_with free g /\ well_formed_heap_with free gp /\ blocks_fit gp /\ no_infix_block gp /\
                    (forall (x: obj_addr). in_use free g x ==> Seq.mem x (objects zero_addr g) /\ ~(is_blue x g)) /\
                    BFS.fwd_well_formed ms fwd (rs_of r roots) /\
                    Fwd.fwd_infix_delta ms fwd /\
                    Inj.fwd_normal_injective fwd gp /\
                    Fwd.fwd_noninfix_targets_valid ms fwd gp /\
                    Inj.fwd_normal_targets_disjoint_from_old_nonblue fwd gp g /\
                    RT.ref_table_covers_with free g r.ref_table (Seq.length r.ref_table) /\
                    MCFH.roots_valid_for_minor_collection ms g (rs_of r roots) /\
                    nursery_fields_valid ms))
  = reveal_opaque (`%mctx) (mctx r roots)

let mctx_delta (r: real_state) (roots: seq U64.t)
  : Lemma (requires mctx r roots)
          (ensures Fwd.fwd_infix_delta r.memory.nursery (fwd_of r roots) /\ minor_wf r.memory.nursery)
  = mctx_elim r roots

#push-options "--ifuel 1 --z3rlimit 40"
let mctx_intro (r: real_state) (h: cycle_history) (roots: seq U64.t) (r': real_state)
  : Lemma (requires run_invariant r h /\ minor_step r roots r')
          (ensures mctx r roots /\
                   r'.memory.major == Promote.update_pointers_with (free_of r) (gp_of r roots) (fwd_of r roots) /\
                   r'.memory.nursery == minor_reset r.memory.nursery /\
                   (minor_result r roots).Promote.mc_fwd == fwd_of r roots)
  = let ms = r.memory.nursery in
    let g = r.memory.major in
    let fp = r.free_list in
    let free = free_of r in
    let rs = rs_of r roots in
    GI.phase_shape_collection ms g fp r.phase r.scan_pos;
    GenInv.collection_shape_with_elim r.phase free ms g fp;
    GenInv.major_shape_with_elim r.phase free g fp;
    GenInv.minor_heap_shape_elim ms;
    free_stw_ok ();
    Promote.free_stw_allocations_not_free r.phase;
    CG.cheney_promote_preserves_wf_with r.phase free ms g fp rs;
    wf_with_parts ();
    Fwd.cheney_promote_fwd_infix_delta r.phase ms g fp rs;
    Inj.cheney_promote_fwd_normal_injective r.phase ms g fp rs;
    Fwd.cheney_promote_fwd_noninfix_targets_valid r.phase ms g fp rs;
    Inj.cheney_promote_fwd_normal_targets_disjoint_from_old_nonblue r.phase ms g fp rs;
    reveal_opaque (`%mctx) (mctx r roots)
#pop-options

/// ---------------------------------------------------------------------------
/// The blocks after the collection
/// ---------------------------------------------------------------------------

/// `x` is the copy of a nursery object.
let image (r: real_state) (roots: seq U64.t) (x: obj_addr) : prop =
  exists (m: U64.t). Seq.mem m (minor_objects r.memory.nursery) /\ fwd_of r roots m == (x <: U64.t)

/// The heap after the pointer update.
let gq (r: real_state) (roots: seq U64.t) : GTot heap =
  Promote.update_pointers_with (free_of r) (gp_of r roots) (fwd_of r roots)

/// The update keeps the walk and every header.
let upd_keeps (r: real_state) (roots: seq U64.t) (x: obj_addr)
  : Lemma (requires mctx r roots /\ Seq.mem x (objects zero_addr (gp_of r roots)))
          (ensures Seq.mem x (objects zero_addr (gq r roots)) /\
                   read_word (gq r roots) (hd_address x) == read_word (gp_of r roots) (hd_address x) /\
                   (is_blue x (gq r roots) <==> is_blue x (gp_of r roots)) /\
                   tag_of_object x (gq r roots) == tag_of_object x (gp_of r roots) /\
                   wosize_of_object x (gq r roots) == wosize_of_object x (gp_of r roots) /\
                   (in_use (free_of r) (gq r roots) x <==> in_use (free_of r) (gp_of r roots) x))
  = mctx_elim r roots;
    let gp = gp_of r roots in
    let upd = in_use (free_of r) gp in
    PU.update_walk_preserves_objects gp upd (fwd_of r roots);
    PU.update_walk_preserves_header gp upd (fwd_of r roots) x;
    CG.update_walk_keeps_in_use free_stw gp upd (fwd_of r roots) x;
    CG.update_walk_keeps_in_use (free_of r) gp upd (fwd_of r roots) x;
    tag_of_object_spec x gp; tag_of_object_spec x (gq r roots);
    wosize_of_object_spec x gp; wosize_of_object_spec x (gq r roots)

/// The copy of a nursery object: a new block of the result, not free, with
/// the object's tag and size.
#push-options "--z3rlimit 20"
let image_facts (r: real_state) (roots: seq U64.t) (m: U64.t)
  : Lemma (requires mctx r roots /\ Seq.mem m (minor_objects r.memory.nursery) /\ fwd_of r roots m <> 0UL)
          (ensures is_val_addr (fwd_of r roots m) /\
                   (let x : obj_addr = fwd_of r roots m in
                    let gp = gp_of r roots in
                    let g' = gq r roots in
                    Seq.mem x (objects zero_addr gp) /\ ~(is_infix x gp) /\
                    Seq.mem x (objects zero_addr g') /\ ~(is_blue x g') /\
                    in_use (free_of r) gp x /\
                    ~(Seq.mem x (objects zero_addr r.memory.major) /\ ~(is_blue x r.memory.major)) /\
                    U64.v (tag_of_object x g') == minor_tag r.memory.nursery m /\
                    U64.v (wosize_of_object x g') == minor_wosize r.memory.nursery m))
  = mctx_elim r roots;
    let ms = r.memory.nursery in
    let g = r.memory.major in
    let fp = r.free_list in
    let rs = rs_of r roots in
    let gp = gp_of r roots in
    minor_objects_not_infix ms m;
    assert (~(is_infix_in_minor ms m));
    let x : obj_addr = fwd_of r roots m in
    wf_with_parts ();
    assert (~(is_infix x gp));
    CPF.cheney_promote_fwd_target_no_scan_iff_minor_tag r.phase ms g fp rs m;
    CPF.cheney_promote_fwd_target_tag r.phase ms g fp rs m;
    CG.cheney_promote_image_not_free r.phase (free_of r) ms g fp rs m x;
    upd_keeps r roots x
#pop-options

/// An old block stays, with its header.
#push-options "--z3rlimit 20"
let old_block (r: real_state) (roots: seq U64.t) (y: obj_addr)
  : Lemma (requires mctx r roots /\ Seq.mem y (objects zero_addr r.memory.major) /\ ~(is_blue y r.memory.major))
          (ensures (let g' = gq r roots in
                    Seq.mem y (objects zero_addr g') /\ ~(is_blue y g') /\
                    read_word g' (hd_address y) == read_word r.memory.major (hd_address y) /\
                    tag_of_object y g' == tag_of_object y r.memory.major /\
                    wosize_of_object y g' == wosize_of_object y r.memory.major /\
                    ~(image r roots y)))
  = mctx_elim r roots;
    let ms = r.memory.nursery in
    let g = r.memory.major in
    let fp = r.free_list in
    let rs = rs_of r roots in
    let gp = gp_of r roots in
    CG.cheney_promote_keeps_in_use r.phase free_stw ms g fp rs y;
    GC.Gen.CheneyPreservation.Frame.cheney_promote_frame_old_header r.phase ms g fp rs y;
    upd_keeps r roots y;
    tag_of_object_spec y g; tag_of_object_spec y gp;
    wosize_of_object_spec y g; wosize_of_object_spec y gp;
    let no_img (m: U64.t)
      : Lemma (requires Seq.mem m (minor_objects ms) /\ fwd_of r roots m == (y <: U64.t))
              (ensures False)
      = image_facts r roots m
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires no_img)
#pop-options

/// A block of the result is an old block or a copy.
#push-options "--z3rlimit 20"
let new_block_origin (r: real_state) (roots: seq U64.t) (x: obj_addr)
  : Lemma (requires mctx r roots /\ Seq.mem x (objects zero_addr (gq r roots)) /\ ~(is_blue x (gq r roots)))
          (ensures (Seq.mem x (objects zero_addr r.memory.major) /\ ~(is_blue x r.memory.major)) \/ image r roots x)
  = mctx_elim r roots;
    let ms = r.memory.nursery in
    let g = r.memory.major in
    let fp = r.free_list in
    let rs = rs_of r roots in
    let gp = gp_of r roots in
    CG.update_walk_keeps_in_use free_stw gp (in_use (free_of r) gp) (fwd_of r roots) x;
    CG.cheney_promote_in_use_origin r.phase free_stw ms g fp rs x
#pop-options

/// ---------------------------------------------------------------------------
/// The map after the collection
/// ---------------------------------------------------------------------------

let ids_after (r: real_state) (roots: seq U64.t) (r': real_state) (ids: block_id_map) : block_id_map =
  forwarded r r' (fwd_of r roots) ids

#push-options "--ifuel 1 --z3rlimit 20"
let ids_image (r: real_state) (roots: seq U64.t) (r': real_state) (ids: block_id_map) (m: U64.t)
  : Lemma (requires mctx r roots /\ r'.memory.major == gq r roots /\
                    Seq.mem m (minor_objects r.memory.nursery) /\ fwd_of r roots m <> 0UL)
          (ensures is_val_addr (fwd_of r roots m) /\
                   ids_after r roots r' ids (Major (fwd_of r roots m)) == ids (Nursery m))
  = mctx_elim r roots;
    image_facts r roots m;
    let x : obj_addr = fwd_of r roots m in
    let fwd = fwd_of r roots in
    assert (forwarded_to r fwd x m);
    let o = FStar.IndefiniteDescription.indefinite_description_ghost U64.t (forwarded_to r fwd x) in
    assert (forwarded_to r fwd x o);
    image_facts r roots o;
    assert (o == m)
#pop-options

#push-options "--ifuel 1 --z3rlimit 20"
let ids_not_image (r: real_state) (roots: seq U64.t) (r': real_state) (ids: block_id_map) (x: obj_addr)
  : Lemma (requires mctx r roots /\ r'.memory.major == gq r roots /\ keyed r.memory ids /\ ~(image r roots x))
          (ensures ids_after r roots r' ids (Major x) ==
                   (if FStar.IndefiniteDescription.strong_excluded_middle (is_allocated r'.memory (Major x))
                    then ids (Major x) else None))
  = mctx_elim r roots;
    let fwd = fwd_of r roots in
    let aux (o: U64.t) : Lemma (~(forwarded_to r fwd x o)) =
      if FStar.IndefiniteDescription.strong_excluded_middle (forwarded_to r fwd x o) then
        assert (image r roots x)
    in
    FStar.Classical.forall_intro aux
#pop-options

/// An old block keeps its id; a block that is neither old nor a copy has none.
#push-options "--ifuel 1 --z3rlimit 20"
let ids_old (r: real_state) (roots: seq U64.t) (r': real_state) (ids: block_id_map) (y: obj_addr)
  : Lemma (requires mctx r roots /\ r'.memory.major == gq r roots /\ keyed r.memory ids /\
                    is_allocated r.memory (Major y))
          (ensures ids_after r roots r' ids (Major y) == ids (Major y) /\ is_allocated r'.memory (Major y))
  = mctx_elim r roots;
    old_block r roots y;
    ids_not_image r roots r' ids y

let ids_none (r: real_state) (roots: seq U64.t) (r': real_state) (ids: block_id_map) (x: obj_addr)
  : Lemma (requires mctx r roots /\ r'.memory.major == gq r roots /\ keyed r.memory ids /\
                    ~(is_allocated r.memory (Major x)) /\ ~(image r roots x))
          (ensures ids_after r roots r' ids (Major x) == None)
  = mctx_elim r roots;
    ids_not_image r roots r' ids x
#pop-options

/// ---------------------------------------------------------------------------
/// Fields after the collection
/// ---------------------------------------------------------------------------

/// What the pointer update does to a word: a forwarded nursery pointer
/// becomes its target's address.
let upd_word (fwd: Promote.forwarding_map) (w: U64.t) : GTot U64.t =
  let v = GBase.to_minor_offset w in
  if Promote.is_minor_pointer v && fwd v <> 0UL then fwd v else w

let field_bound (g: heap) (x: obj_addr) (j: nat)
  : Lemma (requires blocks_fit g /\ Seq.mem x (objects zero_addr g) /\ j < U64.v (wosize_of_object x g))
          (ensures U64.v x + j * 8 + 8 <= heap_size /\ (U64.v x + j * 8) % 8 == 0)
  = hd_address_spec x

/// A field of an old block that is not free at the phase.
#push-options "--z3rlimit 30"
let field_old (r: real_state) (roots: seq U64.t) (y: obj_addr) (j: nat)
  : Lemma (requires mctx r roots /\ in_use (free_of r) r.memory.major y /\ scannable r.memory.major y /\
                    j < U64.v (wosize_of_object y r.memory.major))
          (ensures major_field (gq r roots) y j == upd_word (fwd_of r roots) (major_field r.memory.major y j))
  = mctx_elim r roots;
    let ms = r.memory.nursery in
    let g = r.memory.major in
    let fp = r.free_list in
    let rs = rs_of r roots in
    let gp = gp_of r roots in
    wf_with_parts ();
    field_bound g y j;
    old_block r roots y;
    GC.Gen.CheneyPreservation.Frame.cheney_promote_frame_old_fields r.phase ms g fp rs y j;
    GC.Gen.CheneyPreservation.Frame.cheney_promote_frame_old_header r.phase ms g fp rs y;
    CG.cheney_promote_keeps_in_use r.phase (free_of r) ms g fp rs y;
    is_no_scan_spec y g; is_no_scan_spec y gp;
    tag_of_object_spec y g; tag_of_object_spec y gp;
    wosize_of_object_spec y g; wosize_of_object_spec y gp;
    PU.update_walk_field_effect gp (in_use (free_of r) gp) (fwd_of r roots) y j
#pop-options

/// A field of the copy of a nursery object.
#push-options "--z3rlimit 30"
let field_image (r: real_state) (roots: seq U64.t) (m: U64.t) (j: nat)
  : Lemma (requires mctx r roots /\ Seq.mem m (minor_objects r.memory.nursery) /\ fwd_of r roots m <> 0UL /\
                    j < minor_wosize r.memory.nursery m)
          (ensures is_val_addr (fwd_of r roots m) /\
                   major_field (gq r roots) (fwd_of r roots m) j ==
                   (if minor_tag r.memory.nursery m < 251
                    then upd_word (fwd_of r roots) (minor_read_field r.memory.nursery m j)
                    else minor_read_field r.memory.nursery m j))
  = mctx_elim r roots;
    let ms = r.memory.nursery in
    let g = r.memory.major in
    let fp = r.free_list in
    let rs = rs_of r roots in
    let gp = gp_of r roots in
    image_facts r roots m;
    let x : obj_addr = fwd_of r roots m in
    wf_with_parts ();
    upd_keeps r roots x;
    field_bound gp x j;
    CPF.cheney_promote_fwd_target_fields_match r.phase ms g fp rs m j;
    CPF.cheney_promote_fwd_target_no_scan_iff_minor_tag r.phase ms g fp rs m;
    if minor_tag ms m < 251 then
      PU.update_walk_field_effect gp (in_use (free_of r) gp) (fwd_of r roots) x j
    else
      PU.update_walk_preserves_skipped_field gp (in_use (free_of r) gp) (fwd_of r roots) x j
#pop-options

/// ---------------------------------------------------------------------------
/// Values after the collection
/// ---------------------------------------------------------------------------

/// The word `w`, if a nursery pointer, was forwarded.
let young_forwarded (r: real_state) (roots: seq U64.t) (w: U64.t) : prop =
  Promote.is_minor_pointer (GBase.to_minor_offset w) ==> fwd_of r roots (GBase.to_minor_offset w) <> 0UL

/// The block `b` holds a faithful copy of `id`.
let faithful_rep (m: real_memory) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map) (b: block_addr) (id: I.obj_id)
  : Lemma (requires copies_faithful m h im ids /\ ids b == Some id /\ faithful_block h b)
          (ensures I.valid_id im id /\ block_rep m ids b (Seq.index im.I.objects id))
  = let p (id: I.obj_id) : prop =
      I.valid_id im id /\ block_header_rep m b (Seq.index im.I.objects id) /\
      (faithful_block h b ==> block_rep m ids b (Seq.index im.I.objects id)) in
    assert (p id)

let header_rep (m: real_memory) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map) (b: block_addr) (id: I.obj_id)
  : Lemma (requires copies_faithful m h im ids /\ ids b == Some id)
          (ensures I.valid_id im id /\ block_header_rep m b (Seq.index im.I.objects id))
  = let p (id: I.obj_id) : prop =
      I.valid_id im id /\ block_header_rep m b (Seq.index im.I.objects id) /\
      (faithful_block h b ==> block_rep m ids b (Seq.index im.I.objects id)) in
    assert (p id)

/// The context of the value lemmas.
[@@"opaque_to_smt"]
let vctx (r: real_state) (roots: seq U64.t) (r': real_state) (h: cycle_history) (im: I.ideal_memory)
         (ids: block_id_map) : prop =
  mctx r roots /\ r'.memory.major == gq r roots /\ keyed r.memory ids /\
  copies_faithful r.memory h im ids /\ I.wf_memory im /\ I.wf_objects im

let vctx_elim (r: real_state) (roots: seq U64.t) (r': real_state) (h: cycle_history) (im: I.ideal_memory)
              (ids: block_id_map)
  : Lemma (requires vctx r roots r' h im ids)
          (ensures mctx r roots /\ r'.memory.major == gq r roots /\ keyed r.memory ids /\
                   copies_faithful r.memory h im ids /\ I.wf_memory im /\ I.wf_objects im)
  = reveal_opaque (`%vctx) (vctx r roots r' h im ids)

let vctx_intro (r: real_state) (roots: seq U64.t) (r': real_state) (h: cycle_history) (im: I.ideal_memory)
               (ids: block_id_map)
  : Lemma (requires mctx r roots /\ r'.memory.major == gq r roots /\ keyed r.memory ids /\
                    copies_faithful r.memory h im ids /\ I.wf_memory im /\ I.wf_objects im)
          (ensures vctx r roots r' h im ids)
  = reveal_opaque (`%vctx) (vctx r roots r' h im ids)

/// A word is unchanged by the update.
let upd_word_word (r: real_state) (roots: seq U64.t) (w: U64.t)
  : Lemma (requires outside_heaps w) (ensures upd_word (fwd_of r roots) w == w)
  = ()

let ptr_major_val (x: obj_addr) (k: nat)
  : Lemma (requires U64.v x + 8 * k < pow2 64) (ensures U64.v (ptr_value (Major x) k) == U64.v x + 8 * k)
  = FStar.Math.Lemmas.small_mod (U64.v x + 8 * k) (pow2 64)

/// A pointer into a major block, as a word: above the nursery.
#push-options "--z3rlimit 20"
let major_ptr_word (g: heap) (y: obj_addr) (k: nat)
  : Lemma (requires blocks_fit g /\ Seq.mem y (objects zero_addr g) /\
                    (k == 0 \/ k < U64.v (wosize_of_object y g)))
          (ensures U64.v (ptr_value (Major y) k) == U64.v y + 8 * k /\
                   GBase.to_minor_offset (ptr_value (Major y) k) == ptr_value (Major y) k /\
                   ~(Promote.is_minor_pointer (ptr_value (Major y) k)))
  = objects_addresses_gt_start zero_addr g y;
    hd_address_spec y;
    GBase.zero_addr_above_minor ();
    ptr_major_val y k;
    let w = ptr_value (Major y) k in
    FStar.Math.Lemmas.lemma_mod_plus (U64.v y) k 8;
    GBase.to_minor_offset_stable_above_minor w
#pop-options

/// A pointer into a major block is unchanged, and the block keeps its id.
#push-options "--ifuel 1 --z3rlimit 30"
let upd_word_major (r: real_state) (roots: seq U64.t) (r': real_state) (h: cycle_history) (im: I.ideal_memory)
    (ids: block_id_map) (y: obj_addr) (hd: I.obj_id) (k: nat)
  : Lemma (requires vctx r roots r' h im ids /\ ids (Major y) == Some hd /\
                    I.valid_value im (I.Ptr { head = hd; infix_offset = k }))
          (ensures upd_word (fwd_of r roots) (ptr_value (Major y) k) == ptr_value (Major y) k /\
                   ids_after r roots r' ids (Major y) == Some hd)
  = let g = r.memory.major in
    assert (I.valid_id im hd);
    let ob = Seq.index im.I.objects hd in
    assert (k == 0 \/ k < ob.I.size);
    vctx_elim r roots r' h im ids;
    mctx_elim r roots;
    ids_old r roots r' ids y;
    header_rep r.memory h im ids (Major y) hd;
    assert (U64.v (wosize_of_object y g) == ob.I.size);
    wf_with_parts ();
    major_ptr_word g y k
#pop-options

let nursery_ptr0 (o: U64.t)
  : Lemma (requires U64.v o < GBase.minor_heap_size /\ U64.v o % 8 == 0 /\ U64.v o >= 8)
          (ensures ptr_value (Nursery o) 0 == o)
  = NA.nursery_ptr o 0;
    U64.v_inj (ptr_value (Nursery o) 0) o

/// A pointer into a nursery object, as a word.
let nursery_word (ms: minor_state) (o: U64.t) (k: nat)
  : Lemma (requires minor_wf ms /\ Seq.mem o (minor_objects ms) /\ (k == 0 \/ k < minor_wosize ms o))
          (ensures U64.v o + 8 * k < GBase.minor_heap_size /\ U64.v o % 8 == 0 /\ U64.v o >= 8)
  = minor_objects_valid ms o; minor_objects_body_bound ms o

/// An exact infix header at field `k - 1` of a nursery closure: the pointer
/// `k` words in is an infix pointer whose parent is the closure.
#push-options "--z3rlimit 20"
let nursery_infix (ms: minor_state) (o: U64.t) (k: pos) (hdr: U64.t)
  : Lemma (requires minor_wf ms /\ Seq.mem o (minor_objects ms) /\ k < minor_wosize ms o /\
                    U64.v o + 8 * k < GBase.minor_heap_size /\
                    minor_read_field ms o (k - 1) == hdr /\ getTag hdr == infix_tag /\
                    U64.v (getWosize hdr) == k)
          (ensures (let w = U64.uint_to_t (U64.v o + 8 * k) in
                    is_infix_in_minor ms w /\ infix_parent ms w == o))
  = nursery_word ms o k;
    getTag_spec hdr; getWosize_spec hdr; infix_tag_val ();
    let w = U64.uint_to_t (U64.v o + 8 * k) in
    assert (U64.v w - 8 == U64.v o + (k - 1) * 8);
    assert (minor_tag ms w == 249);
    assert (minor_wosize ms w == k);
    FStar.Math.Lemmas.lemma_mod_plus (U64.v o) k 8;
    assert (U64.v w % 8 == 0);
    assert (is_infix_in_minor ms w);
    assert (U64.v (infix_parent ms w) == U64.v o);
    U64.v_inj (infix_parent ms w) o
#pop-options

/// A pointer to a nursery object that was forwarded: its copy.
#push-options "--ifuel 1 --z3rlimit 30"
let upd_word_nursery_core (r: real_state) (roots: seq U64.t) (r': real_state) (ids: block_id_map)
    (o: U64.t) (hd: I.obj_id) (k: nat)
  : Lemma (requires mctx r roots /\ r'.memory.major == gq r roots /\
                    Seq.mem o (minor_objects r.memory.nursery) /\ ids (Nursery o) == Some hd /\
                    (k == 0 \/ (k < minor_wosize r.memory.nursery o /\
                       U64.v o + 8 * k < GBase.minor_heap_size /\
                       is_infix_in_minor r.memory.nursery (U64.uint_to_t (U64.v o + 8 * k)) /\
                       infix_parent r.memory.nursery (U64.uint_to_t (U64.v o + 8 * k)) == o)) /\
                    young_forwarded r roots (ptr_value (Nursery o) k))
          (ensures (let w = ptr_value (Nursery o) k in
                    fwd_of r roots o <> 0UL /\ is_val_addr (fwd_of r roots o) /\
                    upd_word (fwd_of r roots) w == ptr_value (Major (fwd_of r roots o)) k /\
                    ids_after r roots r' ids (Major (fwd_of r roots o)) == Some hd))
  = mctx_delta r roots;
    let ms = r.memory.nursery in
    let fwd = fwd_of r roots in
    nursery_word ms o k;
    NA.nursery_ptr o k;
    let w = ptr_value (Nursery o) k in
    assert (U64.v w == U64.v o + 8 * k);
    assert (fwd w <> 0UL);
    assert (GBase.to_minor_offset w == w);
    assert (upd_word fwd w == fwd w);
    if k = 0 then begin
      nursery_ptr0 o;
      assert (w == o);
      ids_image r roots r' ids o;
      let x : obj_addr = fwd o in
      ptr_major_val x k;
      U64.v_inj (ptr_value (Major x) k) x
    end else begin
      assert (w == U64.uint_to_t (U64.v o + 8 * k));
      assert (fwd o <> 0UL);
      assert (U64.v (fwd w) == U64.v (fwd o) + 8 * k);
      assert (U64.v (fwd w) < pow2 64);
      ids_image r roots r' ids o;
      let x : obj_addr = fwd o in
      ptr_major_val x k;
      U64.v_inj (ptr_value (Major x) k) (fwd w)
    end
#pop-options

#push-options "--ifuel 1 --z3rlimit 30"
let upd_word_nursery_rep (r: real_state) (roots: seq U64.t) (r': real_state) (im: I.ideal_memory)
    (ids: block_id_map) (o: U64.t) (hd: I.obj_id) (k: nat)
  : Lemma (requires mctx r roots /\ r'.memory.major == gq r roots /\
                    Seq.mem o (minor_objects r.memory.nursery) /\ ids (Nursery o) == Some hd /\
                    I.valid_id im hd /\ block_rep r.memory ids (Nursery o) (Seq.index im.I.objects hd) /\
                    I.valid_value im (I.Ptr { head = hd; infix_offset = k }) /\
                    young_forwarded r roots (ptr_value (Nursery o) k))
          (ensures (let w = ptr_value (Nursery o) k in
                    fwd_of r roots o <> 0UL /\ is_val_addr (fwd_of r roots o) /\
                    upd_word (fwd_of r roots) w == ptr_value (Major (fwd_of r roots o)) k /\
                    ids_after r roots r' ids (Major (fwd_of r roots o)) == Some hd))
  = mctx_delta r roots;
    let ms = r.memory.nursery in
    let ob = Seq.index im.I.objects hd in
    if k = 0 then upd_word_nursery_core r roots r' ids o hd k
    else begin
      let k1 : nat = k - 1 in
      assert (k1 < ob.I.size);
      assert (content_rep ids (I.field_at ob k1) (block_field r.memory (Nursery o) k1));
      let I.FValue (I.Word hdr) = I.field_at ob k1 in
      nursery_word ms o k;
      nursery_infix ms o k hdr;
      upd_word_nursery_core r roots r' ids o hd k
    end
#pop-options

let upd_word_nursery (r: real_state) (roots: seq U64.t) (r': real_state) (h: cycle_history) (im: I.ideal_memory)
    (ids: block_id_map) (o: U64.t) (hd: I.obj_id) (k: nat)
  : Lemma (requires vctx r roots r' h im ids /\ ids (Nursery o) == Some hd /\
                    I.valid_value im (I.Ptr { head = hd; infix_offset = k }) /\
                    young_forwarded r roots (ptr_value (Nursery o) k))
          (ensures (let w = ptr_value (Nursery o) k in
                    fwd_of r roots o <> 0UL /\ is_val_addr (fwd_of r roots o) /\
                    upd_word (fwd_of r roots) w == ptr_value (Major (fwd_of r roots o)) k /\
                    ids_after r roots r' ids (Major (fwd_of r roots o)) == Some hd))
  = vctx_elim r roots r' h im ids;
    faithful_rep r.memory h im ids (Nursery o) hd;
    upd_word_nursery_rep r roots r' im ids o hd k

/// **A value, translated before, is translated after**, its nursery target
/// forwarded.
#push-options "--ifuel 1 --z3rlimit 20"
let value_trans (r: real_state) (roots: seq U64.t) (r': real_state) (h: cycle_history) (im: I.ideal_memory)
    (ids: block_id_map) (v: I.value) (w: U64.t)
  : Lemma (requires vctx r roots r' h im ids /\ I.valid_value im v /\ value_rep ids v w /\
                    young_forwarded r roots w)
          (ensures value_rep (ids_after r roots r' ids) v (upd_word (fwd_of r roots) w))
  = vctx_elim r roots r' h im ids;
    match v with
    | I.Word w0 -> upd_word_word r roots w
    | I.Ptr { head; infix_offset } ->
        eliminate exists (b: block_addr). ids b == Some head /\ w == ptr_value b infix_offset
        with begin
          match b with
          | Major y -> upd_word_major r roots r' h im ids y head infix_offset
          | Nursery o ->
              upd_word_nursery r roots r' h im ids o head infix_offset;
              let x : obj_addr = fwd_of r roots o in
              assert (ids_after r roots r' ids (Major x) == Some head /\
                      upd_word (fwd_of r roots) w == ptr_value (Major x) infix_offset)
        end
#pop-options

/// ---------------------------------------------------------------------------
/// Every nursery pointer the program can follow is forwarded
/// ---------------------------------------------------------------------------

/// A collector root that is a nursery pointer is forwarded.
#push-options "--z3rlimit 20"
let root_forwarded (r: real_state) (roots: seq U64.t) (a: U64.t)
  : Lemma (requires mctx r roots /\ Seq.mem a (rs_of r roots) /\ Promote.is_minor_pointer a)
          (ensures fwd_of r roots a <> 0UL)
  = mctx_elim r roots;
    let ms = r.memory.nursery in
    if is_infix_in_minor ms a then ()
    else resolve_minor_non_infix ms a
#pop-options

/// A word of a remembered-set root, or a program root, that is young is forwarded.
let rs_young_forwarded (r: real_state) (roots: seq U64.t) (w: U64.t)
  : Lemma (requires mctx r roots /\ Seq.mem w (rs_of r roots))
          (ensures young_forwarded r roots w)
  = mctx_elim r roots;
    if Promote.is_minor_pointer (GBase.to_minor_offset w) then begin
      NA.young_offset w;
      root_forwarded r roots w
    end

/// A field of a promoted nursery object that is young is forwarded.
#push-options "--z3rlimit 20"
let nursery_field_forwarded (r: real_state) (roots: seq U64.t) (m: U64.t) (j: nat)
  : Lemma (requires mctx r roots /\ Seq.mem m (minor_objects r.memory.nursery) /\ fwd_of r roots m <> 0UL /\
                    j < minor_scan_wosize r.memory.nursery m)
          (ensures young_forwarded r roots (minor_read_field r.memory.nursery m j))
  = mctx_elim r roots;
    let ms = r.memory.nursery in
    let w = minor_read_field ms m j in
    let a = GBase.to_minor_offset w in
    if Promote.is_minor_pointer a then begin
      if is_infix_in_minor ms a then ()
      else begin
        assert (is_young w);
        assert (Seq.mem (resolve_minor ms a) (minor_objects ms));
        resolve_minor_non_infix ms a;
        Reach.minor_successors_char ms m a;
        GBase.is_minor_addr_from_bounds a;
        assert (Seq.mem a (Reach.minor_successors ms m));
        minor_objects_body_bound ms a
      end
    end
#pop-options

/// A field of an old block not free at the phase that is young is forwarded
/// (its slot is remembered).
#push-options "--z3rlimit 30"
let major_field_forwarded (r: real_state) (roots: seq U64.t) (y: obj_addr) (j: nat)
  : Lemma (requires mctx r roots /\ in_use (free_of r) r.memory.major y /\ scannable r.memory.major y /\
                    j < U64.v (wosize_of_object y r.memory.major))
          (ensures young_forwarded r roots (major_field r.memory.major y j))
  = mctx_elim r roots;
    let g = r.memory.major in
    let w = major_field g y j in
    let a = GBase.to_minor_offset w in
    wf_with_parts ();
    field_bound g y j;
    if Promote.is_minor_pointer a then begin
      let rt = r.ref_table in
      let p : hp_addr = U64.uint_to_t (U64.v y + j * 8) in
      assert (w == read_word g p);
      eliminate exists (i: nat). i < Seq.length rt /\ U64.v (Seq.index rt i) == U64.v y + j * 8
      with begin
        U64.v_inj (Seq.index rt i) p;
        MCFH.remembered_slot_targets_mem g rt (Seq.length rt) i;
        FStar.Seq.Properties.lemma_mem_append roots (MCFH.remembered_slot_targets g rt (Seq.length rt));
        assert (Seq.mem a (rs_of r roots));
        root_forwarded r roots a
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Faithful copies after the collection
/// ---------------------------------------------------------------------------

/// A field of an old no-scan block is unchanged.
#push-options "--z3rlimit 30"
let field_old_noscan (r: real_state) (roots: seq U64.t) (y: obj_addr) (j: nat)
  : Lemma (requires mctx r roots /\ Seq.mem y (objects zero_addr r.memory.major) /\ ~(is_blue y r.memory.major) /\
                    ~(scannable r.memory.major y) /\ j < U64.v (wosize_of_object y r.memory.major))
          (ensures major_field (gq r roots) y j == major_field r.memory.major y j)
  = mctx_elim r roots;
    let ms = r.memory.nursery in
    let g = r.memory.major in
    let fp = r.free_list in
    let rs = rs_of r roots in
    let gp = gp_of r roots in
    wf_with_parts ();
    field_bound g y j;
    old_block r roots y;
    GC.Gen.CheneyPreservation.Frame.cheney_promote_frame_old_fields r.phase ms g fp rs y j;
    GC.Gen.CheneyPreservation.Frame.cheney_promote_frame_old_header r.phase ms g fp rs y;
    CG.cheney_promote_keeps_in_use r.phase free_stw ms g fp rs y;
    is_no_scan_spec y g; is_no_scan_spec y gp;
    tag_of_object_spec y g; tag_of_object_spec y gp;
    wosize_of_object_spec y g; wosize_of_object_spec y gp;
    PU.update_walk_preserves_skipped_field gp (in_use (free_of r) gp) (fwd_of r roots) y j
#pop-options

/// A field value of the ideal memory is valid.
let field_value_ok_local (im: I.ideal_memory) (id: I.obj_id) (i: nat)
  : Lemma (requires I.wf_memory im /\ I.valid_id im id /\
                    i < Seq.length (I.field_values (Seq.index im.I.objects id)))
          (ensures I.valid_value im (Seq.index (I.field_values (Seq.index im.I.objects id)) i))
  = let p (id: I.obj_id) (i: nat) : prop =
      I.valid_id im id /\ i < Seq.length (I.field_values (Seq.index im.I.objects id)) /\
      I.valid_value im (Seq.index (I.field_values (Seq.index im.I.objects id)) i) in
    assert (p id i)

/// The ideal object's fields are scannable exactly by its tag.
let scannable_tag (im: I.ideal_memory) (id: I.obj_id)
  : Lemma (requires I.wf_objects im /\ I.valid_id im id)
          (ensures (I.Scannable? (Seq.index im.I.objects id).I.fields <==>
                    U64.v (Seq.index im.I.objects id).I.tag < 251))
  = no_scan_tag_val ()

/// The copy of a promoted nursery object holds it faithfully.
#push-options "--ifuel 1 --z3rlimit 30"
let rep_image (r: real_state) (roots: seq U64.t) (r': real_state) (h: cycle_history) (im: I.ideal_memory)
    (ids: block_id_map) (m: U64.t) (id: I.obj_id)
  : Lemma (requires vctx r roots r' h im ids /\ Seq.mem m (minor_objects r.memory.nursery) /\
                    fwd_of r roots m <> 0UL /\ ids (Nursery m) == Some id)
          (ensures is_val_addr (fwd_of r roots m) /\ I.valid_id im id /\
                   block_rep r'.memory (ids_after r roots r' ids) (Major (fwd_of r roots m))
                     (Seq.index im.I.objects id))
  = vctx_elim r roots r' h im ids;
    let ms = r.memory.nursery in
    faithful_rep r.memory h im ids (Nursery m) id;
    scannable_tag im id;
    image_facts r roots m;
    let x : obj_addr = fwd_of r roots m in
    let ob = Seq.index im.I.objects id in
    let ids' = ids_after r roots r' ids in
    minor_scan_wosize_cases ms m;
    let aux (i: nat{i < ob.I.size})
      : Lemma (content_rep ids' (I.field_at ob i) (block_field r'.memory (Major x) i))
      = field_image r roots m i;
        let w = minor_read_field ms m i in
        assert (content_rep ids (I.field_at ob i) w);
        match ob.I.fields with
        | I.Scannable vs ->
            I.wf_objects im |> ignore;
            nursery_field_forwarded r roots m i;
            let p (id: I.obj_id) (i: nat) : prop =
              I.valid_id im id /\ i < Seq.length (I.field_values (Seq.index im.I.objects id)) /\
              I.valid_value im (Seq.index (I.field_values (Seq.index im.I.objects id)) i) in
            assert (p id i);
            value_trans r roots r' h im ids (Seq.index vs i) w
        | I.NoScan _ -> ()
    in
    FStar.Classical.forall_intro aux
#pop-options

/// A kept old block, not free at the phase, holds its object faithfully.
#push-options "--ifuel 1 --z3rlimit 30"
let rep_old (r: real_state) (roots: seq U64.t) (r': real_state) (h: cycle_history) (im: I.ideal_memory)
    (ids: block_id_map) (y: obj_addr) (id: I.obj_id)
  : Lemma (requires vctx r roots r' h im ids /\ in_use (free_of r) r.memory.major y /\ kept h y /\
                    ids (Major y) == Some id)
          (ensures I.valid_id im id /\
                   block_rep r'.memory (ids_after r roots r' ids) (Major y) (Seq.index im.I.objects id))
  = vctx_elim r roots r' h im ids;
    mctx_elim r roots;
    let g = r.memory.major in
    faithful_rep r.memory h im ids (Major y) id;
    scannable_tag im id;
    old_block r roots y;
    is_no_scan_spec y g;
    no_scan_tag_val ();
    let ob = Seq.index im.I.objects id in
    let ids' = ids_after r roots r' ids in
    let aux (i: nat{i < ob.I.size})
      : Lemma (content_rep ids' (I.field_at ob i) (block_field r'.memory (Major y) i))
      = let w = major_field g y i in
        assert (content_rep ids (I.field_at ob i) w);
        match ob.I.fields with
        | I.Scannable vs ->
            field_old r roots y i;
            major_field_forwarded r roots y i;
            let p (id: I.obj_id) (i: nat) : prop =
              I.valid_id im id /\ i < Seq.length (I.field_values (Seq.index im.I.objects id)) /\
              I.valid_value im (Seq.index (I.field_values (Seq.index im.I.objects id)) i) in
            assert (p id i);
            value_trans r roots r' h im ids (Seq.index vs i) w
        | I.NoScan _ -> field_old_noscan r roots y i
    in
    FStar.Classical.forall_intro aux
#pop-options

/// ---------------------------------------------------------------------------
/// The run invariant's facts used here
/// ---------------------------------------------------------------------------

/// A kept allocated block is not free at the phase.
#push-options "--ifuel 1 --z3rlimit 20"
let kept_in_use (r: real_state) (h: cycle_history) (x: obj_addr)
  : Lemma (requires run_invariant r h /\ kept h x /\ is_allocated r.memory (Major x))
          (ensures in_use (free_of r) r.memory.major x)
  = let g = r.memory.major in
    match r.phase with
    | Ph.Idle -> GI.phase_free_idle ()
    | Ph.Marking -> GI.phase_free_marking ()
    | Ph.Sweeping c ->
        GI.phase_free_sweeping c;
        is_black_iff x g; is_white_iff x g;
        assert (~(SPI.pending_free c g x))
#pop-options

/// The pointer roots are exactly the roots that are pointers.
#push-options "--fuel 1 --ifuel 1"
let rec mem_ptr_values (vs: seq I.value) (x: I.value)
  : Lemma (ensures Seq.mem x (ptr_values vs) <==> I.Ptr? x /\ Seq.mem x vs)
          (decreases Seq.length vs)
  = if Seq.length vs = 0 then ()
    else begin
      mem_ptr_values (Seq.tail vs) x;
      FStar.Seq.Properties.lemma_mem_inversion vs;
      FStar.Seq.Properties.mem_cons (Seq.head vs) (ptr_values (Seq.tail vs))
    end
#pop-options

/// ---------------------------------------------------------------------------
/// What the program can reach is promoted
/// ---------------------------------------------------------------------------

/// The facts the reachability argument uses.
[@@"opaque_to_smt"]
let rctx (r: real_state) (roots: seq U64.t) (r': real_state) (h: cycle_history) (im: I.ideal_memory)
         (ids: block_id_map) : prop =
  vctx r roots r' h im ids /\ run_invariant r h /\ covers_reachable im ids /\
  (forall (x: obj_addr) (id: I.obj_id). ids (Major x) == Some id /\ I.reachable im id ==> kept h x) /\
  roots_represented ids (ptr_values im.I.roots) roots

let rctx_elim (r: real_state) (roots: seq U64.t) (r': real_state) (h: cycle_history) (im: I.ideal_memory)
              (ids: block_id_map)
  : Lemma (requires rctx r roots r' h im ids)
          (ensures vctx r roots r' h im ids /\ run_invariant r h /\ covers_reachable im ids /\
                   (forall (x: obj_addr) (id: I.obj_id). ids (Major x) == Some id /\ I.reachable im id ==> kept h x) /\
                   roots_represented ids (ptr_values im.I.roots) roots)
  = reveal_opaque (`%rctx) (rctx r roots r' h im ids)

/// A value that a nursery block, or a kept major block, or a root holds,
/// pointing into the nursery block `o`: `o` is promoted.
#push-options "--ifuel 1 --z3rlimit 20"
let nursery_target_forwarded (r: real_state) (roots: seq U64.t) (r': real_state) (h: cycle_history)
    (im: I.ideal_memory) (ids: block_id_map) (id: I.obj_id) (k: nat) (w: U64.t) (o: U64.t)
  : Lemma (requires vctx r roots r' h im ids /\ I.valid_value im (I.Ptr { head = id; infix_offset = k }) /\
                    value_rep ids (I.Ptr { head = id; infix_offset = k }) w /\ young_forwarded r roots w /\
                    ids (Nursery o) == Some id)
          (ensures fwd_of r roots o <> 0UL)
  = vctx_elim r roots r' h im ids;
    eliminate exists (b: block_addr). ids b == Some id /\ w == ptr_value b k
    with begin
      assert (b == Nursery o);
      upd_word_nursery r roots r' h im ids o id k
    end
#pop-options

/// An edge out of an object whose block is kept, or promoted: its nursery
/// target is promoted.
#push-options "--ifuel 1 --z3rlimit 30"
let edge_forwarded (r: real_state) (roots: seq U64.t) (r': real_state) (h: cycle_history)
    (im: I.ideal_memory) (ids: block_id_map) (bs: block_addr) (src: I.obj_id) (i: nat) (id: I.obj_id) (o: U64.t)
  : Lemma (requires rctx r roots r' h im ids /\ ids bs == Some src /\ I.valid_id im src /\
                    i < Seq.length (I.field_values (Seq.index im.I.objects src)) /\
                    I.target (Seq.index (I.field_values (Seq.index im.I.objects src)) i) == Some id /\
                    ids (Nursery o) == Some id /\
                    (match bs with
                     | Nursery m -> fwd_of r roots m <> 0UL
                     | Major x -> kept h x))
          (ensures fwd_of r roots o <> 0UL)
  = rctx_elim r roots r' h im ids;
    vctx_elim r roots r' h im ids;
    let ob = Seq.index im.I.objects src in
    let I.Scannable vs = ob.I.fields in
    let v = Seq.index vs i in
    let I.Ptr { head; infix_offset } = v in
    assert (head == id);
    scannable_tag im src;
    field_value_ok_local im src i;
    assert (I.field_at ob i == I.FValue v);
    match bs with
    | Nursery m ->
        faithful_rep r.memory h im ids bs src;
        let w = minor_read_field r.memory.nursery m i in
        assert (content_rep ids (I.field_at ob i) w);
        minor_scan_wosize_cases r.memory.nursery m;
        nursery_field_forwarded r roots m i;
        nursery_target_forwarded r roots r' h im ids id infix_offset w o
    | Major x ->
        kept_in_use r h x;
        faithful_rep r.memory h im ids bs src;
        let g = r.memory.major in
        let w = major_field g x i in
        assert (content_rep ids (I.field_at ob i) w);
        is_no_scan_spec x g;
        no_scan_tag_val ();
        major_field_forwarded r roots x i;
        nursery_target_forwarded r roots r' h im ids id infix_offset w o
#pop-options

/// **Every object the program can reach whose block is in the nursery is
/// promoted.**
#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
let rec reach_forwarded (r: real_state) (roots: seq U64.t) (r': real_state) (h: cycle_history)
    (im: I.ideal_memory) (ids: block_id_map) (n: nat) (id: I.obj_id) (o: U64.t)
  : Lemma (requires rctx r roots r' h im ids /\ I.reach_within im n id /\ ids (Nursery o) == Some id)
          (ensures fwd_of r roots o <> 0UL)
          (decreases n)
  = if n = 0 then begin
      rctx_elim r roots r' h im ids;
      vctx_elim r roots r' h im ids;
      eliminate exists (i: nat). i < Seq.length im.I.roots /\ I.target (Seq.index im.I.roots i) == Some id
      with begin
        let v = Seq.index im.I.roots i in
        let I.Ptr { head; infix_offset } = v in
        assert (I.valid_value im v);
        mem_ptr_values im.I.roots v;
        let i' = FStar.Seq.Properties.index_mem v (ptr_values im.I.roots) in
        let w = Seq.index roots i' in
        assert (value_rep ids v w);
        FStar.Seq.Properties.lemma_mem_append roots
          (MCFH.remembered_slot_targets r.memory.major r.ref_table (Seq.length r.ref_table));
        assert (Seq.mem w (rs_of r roots));
        rs_young_forwarded r roots w;
        nursery_target_forwarded r roots r' h im ids id infix_offset w o
      end
    end else begin
      let n1 : nat = n - 1 in
      assert (I.reach_within im n id <==>
              (I.reach_within im n1 id \/
               (exists (src: I.obj_id). I.reach_within im n1 src /\ I.points_to im src id)));
      eliminate I.reach_within im n1 id \/
                (exists (src: I.obj_id). I.reach_within im n1 src /\ I.points_to im src id)
      with reach_forwarded r roots r' h im ids n1 id o
      and begin
        eliminate exists (src: I.obj_id). I.reach_within im n1 src /\ I.points_to im src id
        with begin
          rctx_elim r roots r' h im ids;
          vctx_elim r roots r' h im ids;
          assert (I.reachable im src);
          eliminate exists (bs: block_addr). ids bs == Some src
          with begin
            eliminate exists (i: nat). i < Seq.length (I.field_values (Seq.index im.I.objects src)) /\
                        I.target (Seq.index (I.field_values (Seq.index im.I.objects src)) i) == Some id
            with begin
              match bs with
              | Nursery m ->
                  reach_forwarded r roots r' h im ids n1 src m;
                  edge_forwarded r roots r' h im ids bs src i id o
              | Major x ->
                  assert (kept h x);
                  edge_forwarded r roots r' h im ids bs src i id o
            end
          end
        end
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// The joint invariant after the collection
/// ---------------------------------------------------------------------------

/// A block with an id after the collection is a copy, with its original's
/// id, or an old block, with its own.
#push-options "--ifuel 1 --z3rlimit 20"
let ids_after_cases (r: real_state) (roots: seq U64.t) (r': real_state) (ids: block_id_map) (x: obj_addr)
                    (id: I.obj_id)
  : Lemma (requires mctx r roots /\ r'.memory.major == gq r roots /\ keyed r.memory ids /\
                    ids_after r roots r' ids (Major x) == Some id)
          (ensures (exists (m: U64.t). Seq.mem m (minor_objects r.memory.nursery) /\ fwd_of r roots m <> 0UL /\
                      fwd_of r roots m == (x <: U64.t) /\ ids (Nursery m) == Some id) \/
                   (is_allocated r.memory (Major x) /\ ids (Major x) == Some id /\ ~(image r roots x)))
  = if FStar.IndefiniteDescription.strong_excluded_middle (image r roots x) then begin
      eliminate exists (m: U64.t). Seq.mem m (minor_objects r.memory.nursery) /\ fwd_of r roots m == (x <: U64.t)
      with ids_image r roots r' ids m
    end else if FStar.IndefiniteDescription.strong_excluded_middle (is_allocated r.memory (Major x)) then
      ids_old r roots r' ids x
    else ids_none r roots r' ids x
#pop-options

/// The map is keyed after the collection.
#push-options "--ifuel 1 --z3rlimit 30"
let keyed_after (r: real_state) (roots: seq U64.t) (r': real_state) (ids: block_id_map)
  : Lemma (requires mctx r roots /\ r'.memory.major == gq r roots /\ keyed r.memory ids /\
                    r'.memory.nursery == minor_reset r.memory.nursery)
          (ensures keyed r'.memory (ids_after r roots r' ids))
  = let ids' = ids_after r roots r' ids in
    let ms = r.memory.nursery in
    let dom (b: block_addr) : Lemma (Some? (ids' b) <==> is_allocated r'.memory b) =
      match b with
      | Nursery o -> minor_reset_objects_not_mem ms o
      | Major x ->
          if FStar.IndefiniteDescription.strong_excluded_middle (image r roots x) then begin
            eliminate exists (m: U64.t). Seq.mem m (minor_objects ms) /\ fwd_of r roots m == (x <: U64.t)
            with begin
              ids_image r roots r' ids m;
              image_facts r roots m
            end
          end else if FStar.IndefiniteDescription.strong_excluded_middle (is_allocated r.memory (Major x)) then
            ids_old r roots r' ids x
          else begin
            ids_none r roots r' ids x;
            if FStar.IndefiniteDescription.strong_excluded_middle (is_allocated r'.memory (Major x)) then
              new_block_origin r roots x
          end
    in
    let inj (b1 b2: block_addr)
      : Lemma (requires Some? (ids' b1) /\ ids' b1 == ids' b2) (ensures b1 == b2)
      = match b1, b2 with
        | Major x1, Major x2 ->
            let id = Some?.v (ids' b1) in
            ids_after_cases r roots r' ids x1 id;
            ids_after_cases r roots r' ids x2 id
        | _, _ -> ()
    in
    FStar.Classical.forall_intro dom;
    FStar.Classical.forall_intro_2 (fun b1 -> FStar.Classical.move_requires (inj b1))
#pop-options

/// The copies are faithful after the collection.
#push-options "--ifuel 1 --z3rlimit 30"
let copies_after_at (r: real_state) (roots: seq U64.t) (r': real_state) (h h': cycle_history) (im: I.ideal_memory)
    (ids: block_id_map) (b: block_addr) (id: I.obj_id)
  : Lemma (requires rctx r roots r' h im ids /\
                    (forall (x: obj_addr). kept h' x /\ is_allocated r.memory (Major x) ==> kept h x) /\
                    ids_after r roots r' ids b == Some id)
          (ensures I.valid_id im id /\ block_header_rep r'.memory b (Seq.index im.I.objects id) /\
                   (faithful_block h' b ==>
                      block_rep r'.memory (ids_after r roots r' ids) b (Seq.index im.I.objects id)))
  = rctx_elim r roots r' h im ids;
    vctx_elim r roots r' h im ids;
    match b with
    | Major x ->
        ids_after_cases r roots r' ids x id;
        if FStar.IndefiniteDescription.strong_excluded_middle (image r roots x) then begin
          eliminate exists (m: U64.t). Seq.mem m (minor_objects r.memory.nursery) /\ fwd_of r roots m <> 0UL /\
                      fwd_of r roots m == (x <: U64.t) /\ ids (Nursery m) == Some id
          with rep_image r roots r' h im ids m id
        end else begin
          header_rep r.memory h im ids (Major x) id;
          old_block r roots x;
          if FStar.IndefiniteDescription.strong_excluded_middle (kept h' x) then begin
            kept_in_use r h x;
            rep_old r roots r' h im ids x id
          end
        end
#pop-options

let copies_after (r: real_state) (roots: seq U64.t) (r': real_state) (h h': cycle_history) (im: I.ideal_memory)
    (ids: block_id_map)
  : Lemma (requires rctx r roots r' h im ids /\
                    (forall (x: obj_addr). kept h' x /\ is_allocated r.memory (Major x) ==> kept h x))
          (ensures copies_faithful r'.memory h' im (ids_after r roots r' ids))
  = let ids' = ids_after r roots r' ids in
    introduce forall (b: block_addr) (id: I.obj_id).
        ids' b == Some id ==>
          I.valid_id im id /\ block_header_rep r'.memory b (Seq.index im.I.objects id) /\
          (faithful_block h' b ==> block_rep r'.memory ids' b (Seq.index im.I.objects id))
    with introduce _ ==> _ with copies_after_at r roots r' h h' im ids b id

/// Every reachable object keeps a block.
#push-options "--ifuel 1 --z3rlimit 30"
let covers_after (r: real_state) (roots: seq U64.t) (r': real_state) (h: cycle_history) (im: I.ideal_memory)
    (ids: block_id_map)
  : Lemma (requires rctx r roots r' h im ids)
          (ensures covers_reachable im (ids_after r roots r' ids))
  = let ids' = ids_after r roots r' ids in
    let aux (id: I.obj_id)
      : Lemma (requires I.reachable im id) (ensures exists (b: block_addr). ids' b == Some id)
      = rctx_elim r roots r' h im ids;
        vctx_elim r roots r' h im ids;
        eliminate exists (b: block_addr). ids b == Some id
        with begin
          match b with
          | Major x -> ids_old r roots r' ids x
          | Nursery o ->
              eliminate exists (n: nat). I.reach_within im n id
              with begin
                reach_forwarded r roots r' h im ids n id o;
                ids_image r roots r' ids o;
                let x : obj_addr = fwd_of r roots o in
                assert (ids' (Major x) == Some id)
              end
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// What the program can reach is kept after the collection.
#push-options "--ifuel 1 --z3rlimit 30"
let reach_kept_after (r: real_state) (roots: seq U64.t) (r': real_state) (h h': cycle_history) (im: I.ideal_memory)
    (ids: block_id_map)
  : Lemma (requires rctx r roots r' h im ids /\
                    (forall (x: obj_addr). kept h x ==> kept h' x) /\
                    (forall (x: obj_addr). is_allocated r'.memory (Major x) /\ ~(is_allocated r.memory (Major x)) ==>
                       kept h' x))
          (ensures forall (x: obj_addr) (id: I.obj_id).
                     ids_after r roots r' ids (Major x) == Some id /\ I.reachable im id ==> kept h' x)
  = let aux (x: obj_addr) (id: I.obj_id)
      : Lemma (requires ids_after r roots r' ids (Major x) == Some id /\ I.reachable im id) (ensures kept h' x)
      = rctx_elim r roots r' h im ids;
        vctx_elim r roots r' h im ids;
        ids_after_cases r roots r' ids x id;
        if FStar.IndefiniteDescription.strong_excluded_middle (image r roots x) then begin
          eliminate exists (m: U64.t). Seq.mem m (minor_objects r.memory.nursery) /\ fwd_of r roots m <> 0UL /\
                      fwd_of r roots m == (x <: U64.t) /\ ids (Nursery m) == Some id
          with image_facts r roots m
        end
    in
    FStar.Classical.forall_intro_2 (fun x -> FStar.Classical.move_requires (aux x))
#pop-options

let rctx_intro (r: real_state) (roots: seq U64.t) (r': real_state) (h: cycle_history) (im: I.ideal_memory)
               (ids: block_id_map)
  : Lemma (requires vctx r roots r' h im ids /\ run_invariant r h /\ covers_reachable im ids /\
                    (forall (x: obj_addr) (id: I.obj_id). ids (Major x) == Some id /\ I.reachable im id ==> kept h x) /\
                    roots_represented ids (ptr_values im.I.roots) roots)
          (ensures rctx r roots r' h im ids)
  = reveal_opaque (`%rctx) (rctx r roots r' h im ids)

/// Idle, the map's major blocks are the kept ones.
#push-options "--ifuel 1 --z3rlimit 20"
let retains_after (r': real_state) (h': cycle_history) (ids': block_id_map)
  : Lemma (requires run_invariant r' h' /\ keyed r'.memory ids')
          (ensures retains_snapshot r' h' ids')
  = ()
#pop-options

#push-options "--ifuel 1 --z3rlimit 40"
let minor_keeps r h im ids roots r' =
  let h' = update_history h r (Minor roots) r' in
  let ids' = update_block_ids ids (Seq.length im.I.objects) r (Minor roots) r' in
  assert (minor_step r roots r');
  mctx_intro r h roots r';
  minor_keeps_run_invariant r h roots r';
  assert (ids' == ids_after r roots r' ids);
  vctx_intro r roots r' h im ids;
  rctx_intro r roots r' h im ids;
  keyed_after r roots r' ids;
  assert (forall (x: obj_addr). kept h' x <==> kept h x \/ made r r' x);
  copies_after r roots r' h h' im ids;
  covers_after r roots r' h im ids;
  reach_kept_after r roots r' h h' im ids;
  retains_after r' h' ids';
  assert (represents r' h' im ids')
#pop-options
