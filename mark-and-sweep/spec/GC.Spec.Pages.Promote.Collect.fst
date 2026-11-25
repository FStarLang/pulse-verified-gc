/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Promote.Collect - the minor collection, for any allocator
/// ---------------------------------------------------------------------------
///
/// Plan §27.2.  From `GC.Spec.Pages.Promote.Loop`'s invariant at the end of
/// promotion, the facts of the whole collection (`collect`):
///
///   * every forwarding target is a block in use, or a valid interior
///     pointer into one, for any definition of free under which the copies
///     are in use (`fwd_targets`) -- akhil's
///     `GC.Gen.CheneyGeneric.cheney_promote_fwd_targets_not_free`;
///   * the heap after promotion is well formed for any such definition of
///     free under which the heap before was, the nursery's major pointers
///     were not free, and every block in use for it is in use for the
///     allocator (`promoted_wf`) -- akhil's `cheney_promote_preserves_wf_with`;
///   * so the pointer update (akhil's, unchanged) keeps well-formedness
///     (`GC.Gen.CheneyGeneric.update_pointers_with_preserves_wf`), and the
///     allocator's invariant (`collect_inv`);
///   * the blocks in use after are the old ones, with their headers and
///     their major pointers, and the copies (`collect_old`, `collect_new`).

module GC.Spec.Pages.Promote.Collect

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Spec.Pages.Promote
open GC.Spec.Pages.Promote.Loop

module U64 = FStar.UInt64
module I = GC.Spec.AllocIface
module AT = GC.Spec.Pages.AllocTag
module Sh = GC.Spec.Pages.Shape
module GenInv = GC.Gen.HeapInvariant
module CV = GC.Gen.CheneyGeneric
module PUpd = GC.Gen.PromoteUpdate

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

/// Under `un`, every block of the allocator's colour in use for the
/// allocator is in use: the copies are not free for `un`.
let copies_in_use (#s: Type0) (a: tal s) (un: free_def) : prop =
  forall (g: heap) (x: obj_addr). in_use a.free g x /\ color_of_object x g == a.col ==> in_use un g x

let copies_in_use_self (#s: Type0) (a: tal s) : Lemma (copies_in_use a a.free) = ()

/// ---------------------------------------------------------------------------
/// Forwarding targets
/// ---------------------------------------------------------------------------

let k_arith (wm: nat{wm >= 1}) (p m: nat)
  : Lemma (requires m - p == wm * 8) (ensures p + (wm - 1) * 8 == m - 8)
  = ()

/// The header of a nursery address is a field of the object it lies in.
let minor_hdr_field (minor: minor_state) (m p: U64.t) (k: nat)
  : Lemma (requires U64.v m >= 8 /\ U64.v m < minor_heap_size /\ U64.v m % 8 == 0 /\
                    U64.v p + k * 8 == U64.v m - 8)
          (ensures minor_tag minor m == U64.v (U64.logand (minor_read_field minor p k) 0xFFUL) /\
                   minor_wosize minor m == U64.v (U64.shift_right (minor_read_field minor p k) 10ul))
  = assert (U64.uint_to_t (U64.v p + k * 8) == U64.uint_to_t (U64.v m - 8))

/// The header word of an infix nursery address, in the nursery and in the
/// copy of its closure.
#push-options "--z3rlimit 40"
let infix_word (#s: Type0) (a: tal s) (minor: minor_state) (g0 g: heap) (fwd: forwarding_map) (m: U64.t)
  : Lemma (requires mpre minor /\ is_infix_in_minor minor m /\ fwd m <> 0UL /\ entry a minor g0 g fwd m)
          (ensures (let p = infix_parent minor m in
                    let xp = U64.v (fwd p) in
                    let wm = minor_wosize minor m in
                    let wp = minor_wosize minor p in
                    wm >= 2 /\ U64.v m - U64.v p == wm * 8 /\ U64.v m - U64.v p < wp * 8 /\
                    xp >= 8 /\ xp % 8 == 0 /\ xp + wp * 8 <= heap_size /\
                    U64.v (fwd m) == xp + wm * 8 /\
                    minor_tag minor p == 247 /\
                    (let w = Sh.hdr g (xp + (wm - 1) * 8) in
                     U64.v (U64.logand w 0xFFUL) == 249 /\
                     U64.v (U64.shift_right w 10ul) == wm)))
  = let p = infix_parent minor m in
    infix_parent_in_minor_objects minor m;
    infix_parent_value minor m;
    let wm = minor_wosize minor m in
    let k = wm - 1 in
    assert (copy_of a minor g0 g p (fwd p));
    assert (k < minor_wosize minor p);
    assert (Sh.hdr g (U64.v (fwd p) + k * 8) == minor_read_field minor p k);
    k_arith wm (U64.v p) (U64.v m);
    minor_hdr_field minor m p k
#pop-options

/// An interior pointer `t`, at word `wm` of the block `xp`, whose header
/// word is an infix header of offset `wm`, in a closure.
#push-options "--z3rlimit 30"
let infix_target_core (g: heap) (xp: obj_addr) (wm wp: nat) (t: obj_addr)
  : Lemma (requires wm >= 2 /\ wm < wp /\ U64.v xp + wp * 8 <= heap_size /\
                    U64.v t == U64.v xp + wm * 8 /\
                    Seq.mem xp (objects zero_addr g) /\ U64.v (wosize_of_object xp g) == wp /\
                    U64.v (tag_of_object xp g) == 247 /\
                    (let w = Sh.hdr g (U64.v xp + (wm - 1) * 8) in
                     U64.v (U64.logand w 0xFFUL) == 249 /\
                     U64.v (U64.shift_right w 10ul) == wm))
          (ensures is_infix t g /\ resolve_object t g == xp /\
                   infix_addr_wf g (objects zero_addr g) t)
  = let w = Sh.hdr g (U64.v xp + (wm - 1) * 8) in
    hd_address_spec t;
    assert (read_word g (hd_address t) == w);
    tag_of_object_spec t g;
    getTag_spec w;
    is_infix_spec t g;
    infix_tag_val ();
    wosize_of_object_spec t g;
    getWosize_spec w;
    parent_closure_addr_nat_spec t g;
    resolve_infix_spec t g;
    is_closure_spec xp g;
    closure_tag_val ();
    infix_addr_wf_intro g (objects zero_addr g) t
#pop-options

let t_bounds (xp wm wp tv: nat)
  : Lemma (requires xp >= 8 /\ xp % 8 == 0 /\ xp + wp * 8 <= heap_size /\ wm * 8 < wp * 8 /\ tv == xp + wm * 8)
          (ensures tv >= 8 /\ tv < heap_size /\ tv % 8 == 0 /\ wm < wp)
  = FStar.Math.Lemmas.lemma_mod_plus xp wm 8

/// An infix forwarding target is a valid interior pointer into its
/// closure's copy, and resolves to it.
#push-options "--z3rlimit 30"
let infix_target (#s: Type0) (a: tal s) (minor: minor_state) (g0 g: heap) (fwd: forwarding_map) (m: U64.t)
  : Lemma (requires mpre minor /\ is_infix_in_minor minor m /\ fwd m <> 0UL /\ entry a minor g0 g fwd m)
          (ensures (let p = infix_parent minor m in
                    U64.v (fwd m) >= 8 /\ U64.v (fwd m) < heap_size /\ U64.v (fwd m) % 8 == 0 /\
                    copy_of a minor g0 g p (fwd p) /\
                    (let t : obj_addr = fwd m in
                     is_infix t g /\
                     resolve_object t g == (fwd p <: U64.t) /\
                     infix_addr_wf g (objects zero_addr g) t)))
  = let p = infix_parent minor m in
    infix_word a minor g0 g fwd m;
    t_bounds (U64.v (fwd p)) (minor_wosize minor m) (minor_wosize minor p) (U64.v (fwd m));
    assert (copy_of a minor g0 g p (fwd p));
    tag_not_infix minor p;
    let xp : obj_addr = fwd p in
    let t : obj_addr = fwd m in
    infix_target_core g xp (minor_wosize minor m) (minor_wosize minor p) t
#pop-options

/// **Every forwarding target is in use** for any definition of free under
/// which the copies are.
#push-options "--z3rlimit 40"
let fwd_targets (#s: Type0) (a: tal s) (un: free_def) (minor: minor_state) (g0 g: heap) (fwd: forwarding_map)
  : Lemma (requires mpre minor /\ free_def_ok a.free /\ no_infix_block g /\ copies_in_use a un /\
                    entries a minor g0 g fwd)
          (ensures CV.fwd_targets_not_free un g fwd)
  = let one (m: U64.t)
      : Lemma (requires fwd m <> 0UL)
              (ensures U64.v (fwd m) >= U64.v mword /\ U64.v (fwd m) < heap_size /\
                       U64.v (fwd m) % U64.v mword == 0 /\
                       in_use un g (resolve_object ((fwd m) <: obj_addr) g) /\
                       infix_addr_wf g (objects zero_addr g) ((fwd m) <: obj_addr))
      = assert (entry a minor g0 g fwd m);
        if is_infix_in_minor minor m then begin
          infix_target a minor g0 g fwd m;
          assert (copy_of a minor g0 g (infix_parent minor m) (fwd (infix_parent minor m)))
        end else begin
          let x : obj_addr = fwd m in
          assert (copy_of a minor g0 g m (fwd m));
          free_def_ok_elim a.free;
          assert (~(is_infix x g));
          resolve_non_infix x g;
          infix_addr_wf_non_infix g (objects zero_addr g) x
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires one)
#pop-options

/// ---------------------------------------------------------------------------
/// Well-formedness after promotion
/// ---------------------------------------------------------------------------

/// A field that `points_to` finds.
#push-options "--fuel 1 --ifuel 0 --z3rlimit 30"
let rec efptu_field (g: heap) (src: obj_addr) (wz: U64.t{U64.v wz < pow2 54}) (dst: obj_addr)
  : Lemma (requires exists_field_pointing_to_unchecked g src wz dst)
          (ensures exists (j: nat). j < U64.v wz /\ Sh.hdr g (U64.v src + j * 8) == (dst <: U64.t) /\
                                is_pointer (dst <: U64.t))
          (decreases U64.v wz)
  = let idx = U64.sub wz 1UL in
    FStar.Math.Lemmas.pow2_plus 54 3;
    assert_norm (pow2 3 == 8);
    assert (U64.v idx * 8 < pow2 57);
    FStar.Math.Lemmas.pow2_lt_compat 64 57;
    FStar.Math.Lemmas.small_mod (U64.v idx * 8) (pow2 64);
    assert (U64.v (U64.mul_mod idx mword) == U64.v idx * 8);
    FStar.Math.Lemmas.pow2_double_sum 57;
    FStar.Math.Lemmas.pow2_lt_compat 64 58;
    FStar.Math.Lemmas.small_mod (U64.v src + U64.v idx * 8) (pow2 64);
    let far = U64.add_mod src (U64.mul_mod idx mword) in
    assert (U64.v far == U64.v src + U64.v idx * 8);
    if U64.v far >= heap_size || U64.v far % 8 <> 0 then ()
    else begin
      let fv = read_word g (far <: hp_addr) in
      if is_pointer_to fv dst then begin
        let fo : obj_addr = fv in
        hd_address_spec fo;
        hd_address_spec dst;
        assert (fv == (dst <: U64.t));
        assert (mk_hp_addr (U64.v far) == far)
      end
      else efptu_field g src idx dst
    end
#pop-options

let points_to_field (g: heap) (src dst: obj_addr)
  : Lemma (requires points_to g src dst)
          (ensures exists (j: nat). j < U64.v (wosize_of_object src g) /\
                              Sh.hdr g (U64.v src + j * 8) == (dst <: U64.t) /\ is_pointer (dst <: U64.t))
  = wosize_of_object_bound src g;
    efptu_field g src (wosize_of_object src g) dst

/// A target of an old block, in use for `un` before, stays so.
#push-options "--z3rlimit 40"
let old_target_wf (#s: Type0) (a: tal s) (un: free_def) (g0 g: heap) (dst: obj_addr)
  : Lemma (requires free_def_ok a.free /\ free_def_ok un /\
                    (forall (h: heap) (y: obj_addr). in_use un h y ==> in_use a.free h y) /\
                    olds a g0 g /\ (forall (y: obj_addr). in_use a.free g y ==> Seq.mem y (objects zero_addr g)) /\
                    in_use un g0 (resolve_object dst g0) /\ infix_addr_wf g0 (objects zero_addr g0) dst)
          (ensures in_use un g (resolve_object dst g) /\ infix_addr_wf g (objects zero_addr g) dst /\
                   resolve_object dst g == resolve_object dst g0)
  = let t = resolve_object dst g0 in
    assert (in_use a.free g0 t /\ in_use a.free g t /\ kept g0 g t);
    free_def_ok_elim a.free;
    if is_infix dst g0 then begin
      infix_addr_wf_elim g0 (objects zero_addr g0) dst;
      parent_closure_addr_nat_spec dst g0;
      resolve_infix_spec dst g0;
      hd_address_spec dst;
      wosize_of_object_spec t g0;
      assert (read_word g (hd_address dst) == read_word g0 (hd_address dst));
      resolve_object_locality dst g0 g;
      resolve_object_locality t g0 g;
      infix_addr_wf_transfer g0 g (objects zero_addr g0) (objects zero_addr g) dst
    end else begin
      resolve_non_infix dst g0;
      resolve_object_locality dst g0 g;
      resolve_non_infix dst g;
      infix_addr_wf_non_infix g (objects zero_addr g) dst
    end;
    in_use_is_determined_from_header un g0 g t
#pop-options

/// An old source keeps its edges.
#push-options "--z3rlimit 40"
let old_src (#s: Type0) (a: tal s) (un: free_def) (g0 g: heap) (src dst: obj_addr)
  : Lemma (requires free_def_ok a.free /\ free_def_ok un /\ well_formed_heap_with un g0 /\
                    (forall (h: heap) (y: obj_addr). in_use un h y ==> in_use a.free h y) /\
                    olds a g0 g /\ (forall (y: obj_addr). in_use a.free g y ==> Seq.mem y (objects zero_addr g)) /\
                    in_use a.free g0 src /\ in_use un g src /\ scannable g src /\ points_to g src dst)
          (ensures in_use un g (resolve_object dst g) /\ infix_addr_wf g (objects zero_addr g) dst)
  = assert (kept g0 g src);
    free_def_ok_elim a.free;
    in_use_is_determined_from_header un g0 g src;
    is_no_scan_spec src g0; is_no_scan_spec src g;
    tag_of_object_spec src g0; tag_of_object_spec src g;
    wosize_of_object_spec src g0; wosize_of_object_spec src g;
    wosize_of_object_bound src g0;
    GC.Spec.Pages.Retag.efptu_congr g g0 src (wosize_of_object src g0) dst;
    points_to_target_not_free un g0 src dst;
    old_target_wf a un g0 g dst
#pop-options

/// A copy's edges lead to old blocks in use.
#push-options "--z3rlimit 40"
let new_src (#s: Type0) (a: tal s) (un: free_def) (minor: minor_state) (g0 g: heap) (m: U64.t) (src dst: obj_addr)
  : Lemma (requires free_def_ok a.free /\ free_def_ok un /\ well_formed_heap_with un g0 /\
                    GenInv.minor_major_fields_not_free un minor g0 /\
                    (forall (h: heap) (y: obj_addr). in_use un h y ==> in_use a.free h y) /\
                    olds a g0 g /\ copy_of a minor g0 g m (src <: U64.t) /\
                    scannable g src /\ points_to g src dst)
          (ensures in_use un g (resolve_object dst g) /\ infix_addr_wf g (objects zero_addr g) dst)
  = points_to_field g src dst;
    is_no_scan_spec src g;
    no_scan_tag_val ();
    minor_tag_bound minor m;
    minor_scan_wosize_cases minor m;
    eliminate exists (j: nat). j < U64.v (wosize_of_object src g) /\
                               Sh.hdr g (U64.v src + j * 8) == (dst <: U64.t) /\ is_pointer (dst <: U64.t)
    with begin
      assert (j < minor_scan_wosize minor m);
      assert (minor_read_field minor m j == (dst <: U64.t));
      GenInv.minor_major_fields_not_free_elim un minor g0 m j;
      wf_with_parts ();
      free_def_ok_elim a.free;
      old_target_wf a un g0 g dst
    end
#pop-options

/// **The heap after promotion is well formed** for any definition of free
/// `un` under which the heap before was, the nursery's major pointers were
/// in use, and every block in use is in use for the allocator.  akhil's
/// `GC.Gen.CheneyGeneric.cheney_promote_preserves_wf_with`.
#push-options "--z3rlimit 40"
let promoted_wf (#s: Type0) (a: tal s) (un: free_def) (minor: minor_state) (g0 g: heap) (fwd: forwarding_map)
  : Lemma (requires free_def_ok a.free /\ free_def_ok un /\ well_formed_heap_with un g0 /\
                    well_formed_heap_with a.free g /\
                    GenInv.minor_major_fields_not_free un minor g0 /\
                    (forall (h: heap) (y: obj_addr). in_use un h y ==> in_use a.free h y) /\
                    olds a g0 g /\ news a minor g0 g fwd)
          (ensures well_formed_heap_with un g)
  = wf_with_parts ();
    free_def_ok_elim a.free;
    let tgt (src dst: obj_addr)
      : Lemma (requires in_use un g src /\ scannable g src /\ points_to g src dst)
              (ensures in_use un g (resolve_object dst g) /\ infix_addr_wf g (objects zero_addr g) dst)
      = assert (in_use a.free g src);
        if FStar.IndefiniteDescription.strong_excluded_middle (in_use a.free g0 src)
        then old_src a un g0 g src dst
        else
          eliminate exists (m: U64.t). fwd m == (src <: U64.t) /\ copy_of a minor g0 g m (src <: U64.t)
          with new_src a un minor g0 g m src dst
    in
    pointers_lead_to_non_free_intro un g (fun src dst -> tgt src dst);
    interior_pointers_valid_intro un g (fun src dst -> tgt src dst)
#pop-options

/// ---------------------------------------------------------------------------
/// The whole collection
/// ---------------------------------------------------------------------------

/// The heap promotion leaves, and the collection's.
let pm (#s: Type0) (a: tal s) (minor: minor_state) (g0: heap) (st0: s) (roots: seq U64.t) : GTot heap =
  (promote a minor g0 st0 roots).major

/// What promotion ends in.
#push-options "--z3rlimit 30"
let promoted (#s: Type0) (a: tal s) (minor: minor_state) (g0: heap) (st0: s) (roots: seq U64.t)
  : Lemma (requires cpre a minor g0 st0)
          (ensures (let cs = promote a minor g0 st0 roots in
                    ctx a minor g0 /\ linv a minor g0 cs /\
                    free_def_ok a.free /\ well_formed_heap_with a.free cs.major /\
                    blocks_fit cs.major /\ no_infix_block cs.major /\
                    CV.fwd_targets_not_free a.free cs.major cs.fwd))
  = promote_linv a minor g0 st0 roots;
    let cs = promote a minor g0 st0 roots in
    contract_wf a cs.major cs.st;
    wf_with_parts ();
    copies_in_use_self a;
    fwd_targets a a.free minor g0 cs.major cs.fwd
#pop-options

/// **The minor collection keeps the allocator's invariant and
/// well-formedness**, and the walk and every header of the promoted heap.
#push-options "--z3rlimit 30"
let collect_inv (#s: Type0) (a: tal s) (minor: minor_state) (g0: heap) (st0: s) (roots: seq U64.t)
  : Lemma (requires cpre a minor g0 st0)
          (ensures (let cs = promote a minor g0 st0 roots in
                    let r = collect a minor g0 st0 roots in
                    r.rminor == minor_reset minor /\ r.rst == cs.st /\
                    a.inv r.rmajor r.rst /\ well_formed_heap_with a.free r.rmajor /\
                    objects zero_addr r.rmajor == objects zero_addr cs.major /\
                    (forall (y: obj_addr). Seq.mem y (objects zero_addr cs.major) ==>
                       read_word r.rmajor (hd_address y) == read_word cs.major (hd_address y)) /\
                    (forall (y: obj_addr). in_use a.free r.rmajor y == in_use a.free cs.major y)))
  = promoted a minor g0 st0 roots;
    let cs = promote a minor g0 st0 roots in
    let upd = in_use a.free cs.major in
    CV.update_pointers_with_preserves_wf a.free cs.major cs.fwd;
    free_def_ok_elim a.free;
    assert (walk_ok cs.major upd);
    contract_update a cs.major cs.st upd cs.fwd;
    PUpd.update_walk_preserves_objects cs.major upd cs.fwd;
    let g' = update_walk cs.major upd cs.fwd in
    let hd (y: obj_addr)
      : Lemma (Seq.mem y (objects zero_addr cs.major) ==>
               read_word g' (hd_address y) == read_word cs.major (hd_address y))
      = if Seq.mem y (objects zero_addr cs.major) then
          PUpd.update_walk_preserves_header cs.major upd cs.fwd y
    in
    FStar.Classical.forall_intro hd;
    let iu (y: obj_addr) : Lemma (in_use a.free g' y == in_use a.free cs.major y)
      = if Seq.mem y (objects zero_addr cs.major) then
          in_use_is_determined_from_header a.free g' cs.major y
    in
    FStar.Classical.forall_intro iu
#pop-options

/// **The blocks in use after**: every block in use before stays, with its
/// header; every other one is a copy, in the allocator's colour, of a
/// nursery object the forwarding map sends to it.
#push-options "--z3rlimit 30"
let collect_blocks (#s: Type0) (a: tal s) (minor: minor_state) (g0: heap) (st0: s) (roots: seq U64.t)
                   (y: obj_addr)
  : Lemma (requires cpre a minor g0 st0)
          (ensures (let r = collect a minor g0 st0 roots in
                    (in_use a.free g0 y ==>
                       in_use a.free r.rmajor y /\ read_word r.rmajor (hd_address y) == read_word g0 (hd_address y)) /\
                    (in_use a.free r.rmajor y /\ ~(in_use a.free g0 y) ==>
                       color_of_object y r.rmajor == a.col /\
                       (exists (m: U64.t). r.rfwd m == (y <: U64.t) /\ Seq.mem m (minor_objects minor) /\
                                      ~(is_infix_in_minor minor m)))))
  = promoted a minor g0 st0 roots;
    collect_inv a minor g0 st0 roots;
    let cs = promote a minor g0 st0 roots in
    let r = collect a minor g0 st0 roots in
    free_def_ok_elim a.free;
    if in_use a.free g0 y then assert (kept g0 cs.major y);
    if in_use a.free r.rmajor y && not (in_use a.free g0 y) then begin
      eliminate exists (m: U64.t). cs.fwd m == (y <: U64.t) /\ copy_of a minor g0 cs.major m (y <: U64.t)
      with ();
      color_of_object_spec y cs.major;
      color_of_object_spec y r.rmajor
    end
#pop-options

/// **A major pointer of a block in use before stays**: the update rewrites
/// only nursery pointers, and a major pointer never looks like one.
#push-options "--z3rlimit 30"
let collect_major_field (#s: Type0) (a: tal s) (minor: minor_state) (g0: heap) (st0: s) (roots: seq U64.t)
                        (y: obj_addr) (j: nat)
  : Lemma (requires cpre a minor g0 st0 /\ in_use a.free g0 y /\
                    j < U64.v (wosize_of_object y g0) /\ U64.v y + j * 8 + 8 <= heap_size /\
                    is_pointer (read_word g0 (U64.uint_to_t (U64.v y + j * 8))))
          (ensures read_word (collect a minor g0 st0 roots).rmajor (U64.uint_to_t (U64.v y + j * 8)) ==
                   read_word g0 (U64.uint_to_t (U64.v y + j * 8)))
  = promoted a minor g0 st0 roots;
    let cs = promote a minor g0 st0 roots in
    let upd = in_use a.free cs.major in
    let fa = U64.uint_to_t (U64.v y + j * 8) in
    let w = read_word g0 fa in
    FStar.Math.Lemmas.lemma_mod_plus (U64.v y) j 8;
    assert (kept g0 cs.major y);
    assert (read_word cs.major fa == w);
    free_def_ok_elim a.free;
    wosize_of_object_spec y g0;
    wosize_of_object_spec y cs.major;
    if is_no_scan y cs.major then
      PUpd.update_walk_preserves_skipped_field cs.major upd cs.fwd y j
    else begin
      PUpd.update_walk_field_effect cs.major upd cs.fwd y j;
      GC.Gen.Base.zero_addr_above_minor ();
      GC.Gen.Base.to_minor_offset_stable_above_minor w
    end
#pop-options

/// **What a block in use stores keeps its resolution.**
#push-options "--z3rlimit 40"
let collect_target (#s: Type0) (a: tal s) (minor: minor_state) (g0: heap) (st0: s) (roots: seq U64.t)
                   (w: U64.t)
  : Lemma (requires cpre a minor g0 st0 /\ is_pointer w /\ GC.Spec.SweepPhase.Intrinsic.storable a.free g0 w)
          (ensures resolve_object (w <: obj_addr) (collect a minor g0 st0 roots).rmajor ==
                   resolve_object (w <: obj_addr) g0 /\
                   in_use a.free (collect a minor g0 st0 roots).rmajor (resolve_object (w <: obj_addr) g0))
  = promoted a minor g0 st0 roots;
    collect_inv a minor g0 st0 roots;
    let cs = promote a minor g0 st0 roots in
    let upd = in_use a.free cs.major in
    let h : obj_addr = w in
    free_def_ok_elim a.free;
    contract_wf a g0 st0;
    old_target_wf a a.free g0 cs.major h;
    let t = resolve_object h cs.major in
    (if is_infix h cs.major then infix_addr_wf_elim cs.major (objects zero_addr cs.major) h
     else resolve_non_infix h cs.major);
    CV.update_walk_frame_target_header cs.major upd cs.fwd h;
    resolve_object_locality h cs.major (collect a minor g0 st0 roots).rmajor
#pop-options
