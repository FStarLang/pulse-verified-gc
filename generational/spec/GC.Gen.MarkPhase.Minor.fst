module GC.Gen.MarkPhase.Minor

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.MinorHeap

module U64 = FStar.UInt64
module GenInv = GC.Gen.HeapInvariant
module Ph = GC.Spec.Phase
module Cheney = GC.Gen.Cheney
module Promote = GC.Gen.Promote
module MP = GC.Spec.MarkPhase
module MCFH = GC.Gen.MinorCollectForwarding.Helpers
module SPI = GC.Spec.SweepPhase.Intrinsic
module MM = GC.Spec.MarkPhase.Mutator
module AP = GC.Spec.Allocator.Phase
module AllocLemmas = GC.Spec.Allocator.Lemmas
module CV = GC.Gen.CheneyGeneric
module CS = GC.Gen.Cheney.Steps
module Frame = GC.Gen.CheneyPreservation.Frame
module PUpd = GC.Gen.PromoteUpdate
module Edges = GC.Gen.MinorCollectForwarding.Edges
module Mark = GC.Spec.Mark
module FT = GC.Spec.FieldTarget
module W = GC.Spec.Walk
module GB = GC.Gen.Base
module SA = GC.Spec.Allocator

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10"

let nursery_held_reset minor w =
  FStar.Classical.forall_intro (minor_reset_objects_not_mem minor)

/// An element of a sequence is a member of it.
#push-options "--fuel 1 --ifuel 1"
let rec mem_of_index (#a: eqtype) (s: seq a) (i: nat{i < Seq.length s})
  : Lemma (ensures Seq.mem (Seq.index s i) s) (decreases i)
  = if i = 0 then ()
    else begin
      mem_of_index (Seq.tail s) (i - 1);
      FStar.Seq.Properties.lemma_tl (Seq.head s) (Seq.tail s);
      FStar.Seq.Properties.mem_cons (Seq.head s) (Seq.tail s);
      assert (Seq.equal s (Seq.cons (Seq.head s) (Seq.tail s)))
    end
#pop-options

/// ---------------------------------------------------------------------------
/// What the collection starts from
/// ---------------------------------------------------------------------------

let pre (minor: minor_state) (g: heap) (fp: U64.t) : prop =
  GenInv.collection_shape_with Ph.Marking free_stw minor g fp

#push-options "--z3rlimit 20"
let pre_facts (minor: minor_state) (g: heap) (fp: U64.t)
  : Lemma (requires pre minor g fp)
          (ensures well_formed_heap g /\ blocks_fit g /\ no_infix_block g /\
                   AllocLemmas.fl_valid g fp heap_words /\
                   AllocLemmas.fl_chain_terminates g fp heap_words /\
                   Promote.chain_objects_blue g fp /\
                   minor_infix_wf minor /\ minor_wf minor /\
                   CV.promote_pre minor g fp /\
                   GenInv.major_shape_with Ph.Marking free_stw g fp /\
                   GenInv.minor_heap_shape minor /\
                   GenInv.minor_major_fields_not_free free_stw minor g)
  = GenInv.collection_shape_with_elim Ph.Marking free_stw minor g fp;
    GenInv.major_shape_with_elim Ph.Marking free_stw g fp;
    GenInv.minor_heap_shape_elim minor
#pop-options

let prom (minor: minor_state) (g: heap) (fp: U64.t) (roots: seq U64.t) : GTot Promote.promote_all_result =
  Cheney.cheney_promote Ph.Marking minor g fp roots

/// ---------------------------------------------------------------------------
/// Old blocks
/// ---------------------------------------------------------------------------

/// Every non-free block stays, with its header.
#push-options "--z3rlimit 20"
let old_block (minor: minor_state) (g: heap) (fp: U64.t) (roots: seq U64.t) (y: obj_addr)
  : Lemma (requires pre minor g fp /\ in_use free_stw g y)
          (ensures (let p = prom minor g fp roots in
                    let g' = (collect_marking minor g fp roots).Promote.mc_major in
                    blocks_fit p.Promote.major_final /\
                    in_use free_stw p.Promote.major_final y /\
                    read_word p.Promote.major_final (hd_address y) == read_word g (hd_address y) /\
                    objects zero_addr g' == objects zero_addr p.Promote.major_final /\
                    Seq.mem y (objects zero_addr g') /\
                    read_word g' (hd_address y) == read_word g (hd_address y)))
  = let p = prom minor g fp roots in
    let pm = p.Promote.major_final in
    pre_facts minor g fp;
    free_stw_ok ();
    CV.cheney_promote_keeps_in_use Ph.Marking free_stw minor g fp roots y;
    Frame.cheney_promote_frame_old_header Ph.Marking minor g fp roots y;
    CS.cheney_promote_preserves_wfh_part1 Ph.Marking minor g fp roots;
    PUpd.update_walk_preserves_objects pm (in_use free_stw pm) p.Promote.fwd_map;
    PUpd.update_walk_preserves_header pm (in_use free_stw pm) p.Promote.fwd_map y
#pop-options

/// A pointer field of a non-free block is unchanged: the update rewrites only
/// nursery pointers, and a major pointer never looks like one.
#push-options "--z3rlimit 30"
let old_pointer_field (minor: minor_state) (g: heap) (fp: U64.t) (roots: seq U64.t) (y: obj_addr) (j: nat)
  : Lemma (requires pre minor g fp /\ in_use free_stw g y /\
                    j < U64.v (wosize_of_object y g) /\ U64.v y + j * 8 + 8 <= heap_size /\
                    is_pointer (read_word g (U64.uint_to_t (U64.v y + j * 8))))
          (ensures (let g' = (collect_marking minor g fp roots).Promote.mc_major in
                    read_word g' (U64.uint_to_t (U64.v y + j * 8)) ==
                    read_word g (U64.uint_to_t (U64.v y + j * 8))))
  = let p = prom minor g fp roots in
    let pm = p.Promote.major_final in
    let fa = U64.uint_to_t (U64.v y + j * 8) in
    let w = read_word g fa in
    old_block minor g fp roots y;
    pre_facts minor g fp;
    Frame.cheney_promote_frame_old_fields Ph.Marking minor g fp roots y j;
    MM.header_kept_facts g pm y;
    if is_no_scan y pm then
      PUpd.update_walk_preserves_skipped_field pm (in_use free_stw pm) p.Promote.fwd_map y j
    else begin
      PUpd.update_walk_field_effect pm (in_use free_stw pm) p.Promote.fwd_map y j;
      GB.zero_addr_above_minor ();
      GB.to_minor_offset_stable_above_minor w
    end
#pop-options

/// What a non-free block stores keeps its resolution.
#push-options "--z3rlimit 20"
let old_target (minor: minor_state) (g: heap) (fp: U64.t) (roots: seq U64.t) (w: U64.t)
  : Lemma (requires pre minor g fp /\ is_pointer w /\ SPI.storable free_stw g w)
          (ensures resolve_object (w <: obj_addr) (collect_marking minor g fp roots).Promote.mc_major ==
                   resolve_object (w <: obj_addr) g)
  = pre_facts minor g fp;
    free_stw_ok ();
    free_def_ok_elim free_stw;
    Edges.cheney_collect_frame_target_header Ph.Marking minor g fp free_stw roots (w <: obj_addr)
#pop-options

/// ---------------------------------------------------------------------------
/// New blocks are black
/// ---------------------------------------------------------------------------

/// "Free" is "not black": the blocks non-free for it are the black ones.
let free_unless_black : free_def = fun g x -> not (is_black x g)

let free_unless_black_ok (_: unit) : Lemma (free_def_ok free_unless_black)
  = reveal_opaque (`%free_def_ok) free_def_ok;
    let det (g g': heap) (x: obj_addr)
      : Lemma (read_word g (hd_address x) == read_word g' (hd_address x) ==>
               free_unless_black g x == free_unless_black g' x)
      = if read_word g (hd_address x) = read_word g' (hd_address x) then MM.header_kept_facts g g' x
    in
    FStar.Classical.forall_intro_3 det;
    let blu (g: heap) (x: obj_addr) : Lemma (is_blue x g ==> free_unless_black g x) =
      Mark.colors_exclusive x g
    in
    FStar.Classical.forall_intro_2 blu

/// A block allocated while marking is black.
let marking_allocation_black (g: heap) (fp: U64.t) (wz: nat) (tag: U64.t{U64.v tag < 256}) (x: obj_addr)
  : Lemma (requires AP.alloc_ok g fp /\ (AP.alloc_at Ph.Marking g fp wz tag).SA.obj_out == x)
          (ensures is_black x (AP.alloc_at Ph.Marking g fp wz tag).SA.heap_out /\
                   ~(is_blue x (AP.alloc_at Ph.Marking g fp wz tag).SA.heap_out))
  = AP.alloc_at_recoloured Ph.Marking g fp wz tag

let black_allocations (_: unit) : Lemma (Promote.allocations_not_free Ph.Marking free_unless_black)
  = Promote.allocations_not_free_intro Ph.Marking free_unless_black
      (fun g fp wz tag x -> marking_allocation_black g fp wz tag x)

/// Every non-free block of the heap after that was not one before is a
/// promoted copy, black.
#push-options "--z3rlimit 30"
let new_block_black (minor: minor_state) (g: heap) (fp: U64.t) (roots: seq U64.t) (y: obj_addr)
  : Lemma (requires pre minor g fp /\
                    in_use free_stw (collect_marking minor g fp roots).Promote.mc_major y /\
                    ~(in_use free_stw g y))
          (ensures is_black y (collect_marking minor g fp roots).Promote.mc_major)
  = let p = prom minor g fp roots in
    let pm = p.Promote.major_final in
    let g' = (collect_marking minor g fp roots).Promote.mc_major in
    pre_facts minor g fp;
    free_stw_ok ();
    free_unless_black_ok ();
    black_allocations ();
    CS.cheney_promote_preserves_wfh_part1 Ph.Marking minor g fp roots;
    CV.update_walk_keeps_in_use free_stw pm (in_use free_stw pm) p.Promote.fwd_map y;
    CV.cheney_promote_in_use_origin Ph.Marking free_stw minor g fp roots y;
    assert (exists (m: U64.t). Seq.mem m (minor_objects minor) /\ p.Promote.fwd_map m == y);
    eliminate exists (m: U64.t). Seq.mem m (minor_objects minor) /\ p.Promote.fwd_map m == y
    with CV.cheney_promote_image_not_free Ph.Marking free_unless_black minor g fp roots m y;
    free_def_ok_elim free_stw;
    PUpd.update_walk_preserves_header pm (in_use free_stw pm) p.Promote.fwd_map y;
    MM.header_kept_facts pm g' y
#pop-options

/// ---------------------------------------------------------------------------
/// Black objects' white targets: through `MP.unreached g`
/// ---------------------------------------------------------------------------

/// Two blocks whose header and fields agree.
#push-options "--z3rlimit 20"
let same_block_of_fields (g1 g2: heap) (x: obj_addr)
  : Lemma (requires read_word g2 (hd_address x) == read_word g1 (hd_address x) /\
                    U64.v x + U64.v (wosize_of_object x g1) * 8 <= heap_size /\
                    (forall (j: nat). j < U64.v (wosize_of_object x g1) /\ U64.v x + j * 8 + 8 <= heap_size ==>
                       read_word g2 (U64.uint_to_t (U64.v x + j * 8)) ==
                       read_word g1 (U64.uint_to_t (U64.v x + j * 8))))
          (ensures SPI.same_block g1 g2 (hd_address x))
  = hd_address_spec x;
    SPI.colour_of g1 x;
    let f (a: hp_addr)
      : Lemma (requires U64.v (hd_address x) < U64.v a /\ U64.v a < W.bnext g1 (hd_address x))
              (ensures read_word g2 a == read_word g1 a)
      = FStar.Math.Lemmas.lemma_div_exact (U64.v a - U64.v x) 8;
        let j : nat = (U64.v a - U64.v x) / 8 in
        assert (U64.v x + j * 8 == U64.v a);
        assert (U64.uint_to_t (U64.v x + j * 8) == a)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires f)
#pop-options

/// The pointer update at `free_stw` and at a smaller definition of free
/// agree on the blocks the smaller one keeps.
#push-options "--z3rlimit 30"
let update_agrees (pm: heap) (un: free_def) (fwd: Promote.forwarding_map) (x: obj_addr)
  : Lemma (requires blocks_fit pm /\ free_def_ok un /\
                    in_use un (Promote.update_walk pm (in_use un pm) fwd) x)
          (ensures (let gS = Promote.update_walk pm (in_use un pm) fwd in
                    let g' = Promote.update_walk pm (in_use free_stw pm) fwd in
                    SPI.same_block gS g' (hd_address x)))
  = let gS = Promote.update_walk pm (in_use un pm) fwd in
    let g' = Promote.update_walk pm (in_use free_stw pm) fwd in
    free_stw_ok ();
    free_def_ok_elim un;
    PUpd.update_walk_preserves_objects pm (in_use un pm) fwd;
    PUpd.update_walk_preserves_objects pm (in_use free_stw pm) fwd;
    PUpd.update_walk_preserves_header pm (in_use un pm) fwd x;
    PUpd.update_walk_preserves_header pm (in_use free_stw pm) fwd x;
    in_use_is_determined_from_header un gS pm x;
    MM.header_kept_facts pm gS x;
    MM.header_kept_facts pm g' x;
    let fld (j: nat)
      : Lemma (j < U64.v (wosize_of_object x gS) /\ U64.v x + j * 8 + 8 <= heap_size ==>
               read_word g' (U64.uint_to_t (U64.v x + j * 8)) ==
               read_word gS (U64.uint_to_t (U64.v x + j * 8)))
      = if j < U64.v (wosize_of_object x gS) && U64.v x + j * 8 + 8 <= heap_size then begin
          if is_no_scan x pm then begin
            PUpd.update_walk_preserves_skipped_field pm (in_use un pm) fwd x j;
            PUpd.update_walk_preserves_skipped_field pm (in_use free_stw pm) fwd x j
          end else begin
            PUpd.update_walk_field_effect pm (in_use un pm) fwd x j;
            PUpd.update_walk_field_effect pm (in_use free_stw pm) fwd x j
          end
        end
    in
    FStar.Classical.forall_intro fld;
    hd_address_spec x;
    same_block_of_fields gS g' x
#pop-options

/// The nursery's fields point at blocks the marker will reach, if white.
#push-options "--z3rlimit 20"
let nursery_not_unreached (minor: minor_state) (g: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires pre minor g fp /\ MP.marking_inv g (marking_held minor g roots))
          (ensures GenInv.minor_major_fields_not_free (MP.unreached g) minor g)
  = pre_facts minor g fp;
    let h (obj: U64.t) (j: nat)
      : Lemma (requires Seq.mem obj (minor_objects minor) /\ j < minor_scan_wosize minor obj /\
                        is_pointer_field (minor_read_field minor obj j))
              (ensures in_use (MP.unreached g) g ((minor_read_field minor obj j) <: obj_addr))
      = GenInv.minor_major_fields_not_free_elim free_stw minor g obj j;
        let v : obj_addr = minor_read_field minor obj j in
        assert (nursery_held minor v);
        assert (marking_held minor g roots v)
    in
    GenInv.minor_major_fields_not_free_intro (MP.unreached g) minor g h
#pop-options

/// A block allocated while marking is not free for `unreached`.
let unreached_allocations (g0: heap) : Lemma (Promote.allocations_not_free Ph.Marking (MP.unreached g0))
  = let prf (g: heap) (fp: U64.t) (wz: nat) (tag: U64.t{U64.v tag < 256}) (x: obj_addr)
      : Lemma (requires AP.alloc_ok g fp /\ (AP.alloc_at Ph.Marking g fp wz tag).SA.obj_out == x)
              (ensures not (MP.unreached g0 (AP.alloc_at Ph.Marking g fp wz tag).SA.heap_out x))
      = marking_allocation_black g fp wz tag x;
        Mark.colors_exclusive x (AP.alloc_at Ph.Marking g fp wz tag).SA.heap_out
    in
    Promote.allocations_not_free_intro Ph.Marking (MP.unreached g0) prf

/// **The heap after is well formed for any admissible definition of free**
/// whose allocations while marking are not free, if the heap before is and
/// the nursery's major pointers are not free for it.
#push-options "--z3rlimit 20"
let wf_after_with (un: free_def) (minor: minor_state) (g: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires pre minor g fp /\ free_def_ok un /\ Promote.allocations_not_free Ph.Marking un /\
                    well_formed_heap_with un g /\ GenInv.minor_major_fields_not_free un minor g)
          (ensures well_formed_heap_with un (collect_marking minor g fp roots).Promote.mc_major)
  = let p = prom minor g fp roots in
    let pm = p.Promote.major_final in
    let fwd = p.Promote.fwd_map in
    let res = collect_marking minor g fp roots in
    let g' = res.Promote.mc_major in
    pre_facts minor g fp;
    GenInv.major_shape_with_elim Ph.Marking free_stw g fp;
    GenInv.major_shape_with_intro Ph.Marking un g fp;
    GenInv.collection_shape_with_intro Ph.Marking un minor g fp;
    // the generic theorem, for `unreached g`
    CV.cheney_collect_with_preserves_shape Ph.Marking un minor g fp roots;
    let resS = Cheney.cheney_collect_spec_with Ph.Marking un minor g fp roots in
    let gS = resS.Promote.mc_major in
    GenInv.collection_shape_with_elim Ph.Marking un resS.Promote.mc_minor gS resS.Promote.mc_fp;
    GenInv.major_shape_with_elim Ph.Marking un gS resS.Promote.mc_fp;
    // and for `free_stw`: the heap after has no infix block
    CV.cheney_collect_with_preserves_shape Ph.Marking free_stw minor g fp roots;
    GenInv.collection_shape_with_elim Ph.Marking free_stw res.Promote.mc_minor g' res.Promote.mc_fp;
    GenInv.major_shape_with_elim Ph.Marking free_stw g' res.Promote.mc_fp;
    // the two pointer updates agree on the blocks `unreached g` keeps
    CS.cheney_promote_preserves_wfh_part1 Ph.Marking minor g fp roots;
    PUpd.update_walk_preserves_objects pm (in_use un pm) fwd;
    PUpd.update_walk_preserves_objects pm (in_use free_stw pm) fwd;
    let iu (x: obj_addr) : Lemma (in_use un g' x == in_use un gS x) =
      if Seq.mem x (objects zero_addr pm) then begin
        PUpd.update_walk_preserves_header pm (in_use un pm) fwd x;
        PUpd.update_walk_preserves_header pm (in_use free_stw pm) fwd x;
        in_use_is_determined_from_header un gS g' x
      end
    in
    FStar.Classical.forall_intro iu;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (update_agrees pm un fwd));
    SPI.wf_transport gS g' un un
#pop-options

/// **The heap after is well formed for `unreached g`.**
#push-options "--z3rlimit 20"
let unreached_wf_after (minor: minor_state) (g: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires pre minor g fp /\ MP.marking_inv g (marking_held minor g roots))
          (ensures well_formed_heap_with (MP.unreached g) (collect_marking minor g fp roots).Promote.mc_major)
  = MP.unreached_ok g;
    MP.marking_inv_unreached g (marking_held minor g roots);
    unreached_allocations g;
    nursery_not_unreached minor g fp roots;
    wf_after_with (MP.unreached g) minor g fp roots
#pop-options

/// ---------------------------------------------------------------------------
/// The rewritten roots
/// ---------------------------------------------------------------------------

/// A white object a rewritten root holds was held by an old root.
#push-options "--z3rlimit 40"
let rewritten_root (minor: minor_state) (g: heap) (fp: U64.t) (roots: seq U64.t) (r': U64.t) (w: obj_addr)
  : Lemma (requires pre minor g fp /\ MCFH.roots_valid_for_minor_collection minor g roots /\
                    (let res = collect_marking minor g fp roots in
                     Seq.mem r' res.Promote.mc_roots /\ is_pointer r' /\
                     resolve_object (r' <: obj_addr) res.Promote.mc_major == w /\
                     Seq.mem w (objects zero_addr res.Promote.mc_major) /\
                     is_white w res.Promote.mc_major))
          (ensures roots_held g roots w)
  = let p = prom minor g fp roots in
    let pm = p.Promote.major_final in
    let fwd = p.Promote.fwd_map in
    let res = collect_marking minor g fp roots in
    let g' = res.Promote.mc_major in
    pre_facts minor g fp;
    let i = FStar.Seq.Properties.index_mem r' res.Promote.mc_roots in
    Promote.rewrite_roots_index roots fwd i;
    let r = Seq.index roots i in
    mem_of_index roots i;
    GB.zero_addr_above_minor ();
    if Promote.is_minor_pointer r && fwd r <> 0UL then begin
      // a forwarded root: its target is a promoted copy, black
      let h : obj_addr = fwd r in
      free_unless_black_ok ();
      black_allocations ();
      free_def_ok_elim free_unless_black;
      CV.cheney_promote_fwd_targets_not_free Ph.Marking free_unless_black minor g fp roots;
      CS.cheney_promote_preserves_wfh_part1 Ph.Marking minor g fp roots;
      let t = resolve_object h pm in
      (if is_infix h pm then infix_addr_wf_elim pm (objects zero_addr pm) h
       else resolve_non_infix h pm);
      CV.update_walk_frame_target_header pm (in_use free_stw pm) fwd h;
      resolve_object_locality h pm g';
      PUpd.update_walk_preserves_header pm (in_use free_stw pm) fwd t;
      MM.header_kept_facts pm g' t;
      Mark.colors_exclusive t g'
    end else begin
      // an old root, a major block
      assert (r == r');
      resolve_non_infix (r <: obj_addr) g;
      infix_addr_wf_non_infix g (objects zero_addr g) (r <: obj_addr);
      free_stw_ok ();
      old_target minor g fp roots r
    end
#pop-options

/// ---------------------------------------------------------------------------
/// The collection keeps the invariant
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40"
let minor_keeps_marking_inv minor g fp roots =
  let held = marking_held minor g roots in
  let res = collect_marking minor g fp roots in
  let g' = res.Promote.mc_major in
  let held' = roots_held g' res.Promote.mc_roots in
  pre_facts minor g fp;
  CV.cheney_collect_with_preserves_shape Ph.Marking free_stw minor g fp roots;
  GenInv.collection_shape_with_elim Ph.Marking free_stw res.Promote.mc_minor g' res.Promote.mc_fp;
  GenInv.major_shape_with_elim Ph.Marking free_stw g' res.Promote.mc_fp;
  free_stw_ok ();
  wf_with_parts ();
  // grey or white blocks stay, with their colours
  let gw (y: obj_addr)
    : Lemma (requires MP.grey_or_white g y)
            (ensures MP.grey_or_white g' y /\ (is_gray y g ==> is_gray y g'))
    = Mark.colors_exclusive y g;
      old_block minor g fp roots y;
      MM.header_kept_facts g g' y
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires gw);
  // nothing new is white
  let wh (y: obj_addr)
    : Lemma (requires Seq.mem y (objects zero_addr g') /\ is_white y g')
            (ensures Seq.mem y (objects zero_addr g) /\ is_white y g)
    = Mark.colors_exclusive y g';
      if in_use free_stw g y then begin
        old_block minor g fp roots y;
        MM.header_kept_facts g g' y
      end else new_block_black minor g fp roots y
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires wh);
  // no edge out of a grey or white block is cut
  let cut (s t: obj_addr)
    : Lemma (requires MP.grey_or_white g s /\ MP.grey_or_white g t /\ MP.field_edge g s t)
            (ensures MP.field_edge g' s t)
    = Mark.colors_exclusive s g;
      old_block minor g fp roots s;
      MM.header_kept_facts g g' s;
      let fld (j: nat)
        : Lemma (~(is_no_scan s g') /\ j < U64.v (wosize_of_object s g') /\ U64.v s + j * 8 + 8 <= heap_size ==>
                 (let w = read_word g (U64.uint_to_t (U64.v s + j * 8)) in
                  is_pointer w ==>
                  (read_word g' (U64.uint_to_t (U64.v s + j * 8)) == w /\
                   resolve_object (w <: obj_addr) g' == resolve_object (w <: obj_addr) g) \/ False))
        = if not (is_no_scan s g') && j < U64.v (wosize_of_object s g') && U64.v s + j * 8 + 8 <= heap_size then begin
            let w = read_word g (U64.uint_to_t (U64.v s + j * 8)) in
            if is_pointer w then begin
              old_pointer_field minor g fp roots s j;
              FT.wf_with_field free_stw g s j;
              old_target minor g fp roots w
            end
          end
      in
      FStar.Classical.forall_intro fld;
      MM.field_edge_transfer g' g s (fun _ -> False) t
  in
  FStar.Classical.forall_intro_2 (fun s -> FStar.Classical.move_requires (cut s));
  // a black object's white target is one the marker would reach
  unreached_wf_after minor g fp roots;
  let blk (b t: obj_addr)
    : Lemma (requires Seq.mem b (objects zero_addr g') /\ is_black b g' /\ MP.field_edge g' b t /\ is_white t g')
            (ensures MP.marker_will_reach g t)
    = MP.unreached_black_edge g g' b t
  in
  FStar.Classical.forall_intro_2 (fun b -> FStar.Classical.move_requires (blk b));
  // a white object a rewritten root holds was held
  let hr (w: obj_addr)
    : Lemma (requires held' w /\ Seq.mem w (objects zero_addr g') /\ is_white w g')
            (ensures held w)
    = eliminate exists (r': U64.t).
        Seq.mem r' res.Promote.mc_roots /\ is_pointer r' /\ resolve_object (r' <: obj_addr) g' == w
      with rewritten_root minor g fp roots r' w
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires hr);
  MP.marking_inv_change g g' held held'
#pop-options

/// ---------------------------------------------------------------------------
/// The grey objects
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20"
let minor_keeps_greys minor g fp roots y =
  let g' = (collect_marking minor g fp roots).Promote.mc_major in
  free_stw_ok ();
  free_def_ok_elim free_stw;
  Mark.colors_exclusive y g;
  Mark.colors_exclusive y g';
  if Seq.mem y (objects zero_addr g) && is_gray y g then begin
    old_block minor g fp roots y;
    MM.header_kept_facts g g' y
  end;
  if Seq.mem y (objects zero_addr g') && is_gray y g' then begin
    if in_use free_stw g y then begin
      old_block minor g fp roots y;
      MM.header_kept_facts g g' y
    end else
      new_block_black minor g fp roots y
  end
#pop-options

/// ---------------------------------------------------------------------------
/// Blocks and dark fields
/// ---------------------------------------------------------------------------

let minor_keeps_block minor g fp roots y =
  old_block minor g fp roots y

/// A forwarded address resolves, after the collection, to a black block.
#push-options "--z3rlimit 20"
let forwarded_target_black (minor: minor_state) (g: heap) (fp: U64.t) (roots: seq U64.t) (m: U64.t)
  : Lemma (requires pre minor g fp /\ (prom minor g fp roots).Promote.fwd_map m <> 0UL)
          (ensures (let h = (prom minor g fp roots).Promote.fwd_map m in
                    let g' = (collect_marking minor g fp roots).Promote.mc_major in
                    U64.v h >= U64.v mword /\ U64.v h < heap_size /\ U64.v h % U64.v mword == 0 /\
                    is_black (resolve_object (h <: obj_addr) g') g'))
  = let p = prom minor g fp roots in
    let pm = p.Promote.major_final in
    let fwd = p.Promote.fwd_map in
    let g' = (collect_marking minor g fp roots).Promote.mc_major in
    pre_facts minor g fp;
    free_unless_black_ok ();
    black_allocations ();
    free_def_ok_elim free_unless_black;
    CV.cheney_promote_fwd_targets_not_free Ph.Marking free_unless_black minor g fp roots;
    CS.cheney_promote_preserves_wfh_part1 Ph.Marking minor g fp roots;
    let h : obj_addr = fwd m in
    let t = resolve_object h pm in
    (if is_infix h pm then infix_addr_wf_elim pm (objects zero_addr pm) h
     else resolve_non_infix h pm);
    CV.update_walk_frame_target_header pm (in_use free_stw pm) fwd h;
    resolve_object_locality h pm g';
    PUpd.update_walk_preserves_header pm (in_use free_stw pm) fwd t;
    MM.header_kept_facts pm g' t
#pop-options

#push-options "--z3rlimit 20"
let minor_keeps_field_dark minor g fp roots y k =
  let p = prom minor g fp roots in
  let pm = p.Promote.major_final in
  let fwd = p.Promote.fwd_map in
  let g' = (collect_marking minor g fp roots).Promote.mc_major in
  if U64.v (hd_address y) + U64.v mword * U64.v k + U64.v mword <= heap_size then begin
    hd_address_spec y;
    FStar.Math.Lemmas.pow2_plus 3 54;
    assert_norm (pow2 3 == 8);
    assert (U64.v k < pow2 54);
    let j : nat = U64.v k - 1 in
    let fa = U64.uint_to_t (U64.v y + j * 8) in
    GC.Spec.HeapGraph.get_field_addr_eq g y k;
    GC.Spec.HeapGraph.get_field_addr_eq g' y k;
    assert (GC.Spec.HeapGraph.get_field g y k == read_word g fa);
    assert (GC.Spec.HeapGraph.get_field g' y k == read_word g' fa);
    let v = read_word g fa in
    pre_facts minor g fp;
    free_stw_ok ();
    wf_with_parts ();
    old_block minor g fp roots y;
    if is_pointer v then begin
      old_pointer_field minor g fp roots y j;
      FT.wf_with_field free_stw g y j;
      old_target minor g fp roots v;
      let t = resolve_object (v <: obj_addr) g in
      old_block minor g fp roots t;
      MM.header_kept_facts g g' t
    end else begin
      MM.header_kept_facts g pm y;
      Frame.cheney_promote_frame_old_fields Ph.Marking minor g fp roots y j;
      free_def_ok_elim free_stw;
      assert (Seq.mem y (objects zero_addr pm));
      assert (is_no_scan y pm = false);
      assert (j < U64.v (wosize_of_object y pm));
      assert (read_word pm fa == v);
      PUpd.update_walk_field_effect pm (in_use free_stw pm) fwd y j;
      let ov = GB.to_minor_offset v in
      if Promote.is_minor_pointer ov && fwd ov <> 0UL then begin
        assert (read_word g' fa == fwd ov);
        forwarded_target_black minor g fp roots ov;
        Mark.colors_exclusive (resolve_object ((fwd ov) <: obj_addr) g') g'
      end
    end
  end
#pop-options

/// ---------------------------------------------------------------------------
/// For completeness
/// ---------------------------------------------------------------------------

let minor_keeps_wf_with un minor g fp roots = wf_after_with un minor g fp roots

let minor_new_block_black minor g fp roots y = new_block_black minor g fp roots y

let minor_keeps_major_field minor g fp roots y j = old_pointer_field minor g fp roots y j
