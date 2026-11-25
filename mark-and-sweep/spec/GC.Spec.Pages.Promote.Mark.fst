/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Promote.Mark - a minor collection while marking, with pages
/// ---------------------------------------------------------------------------
///
/// Plan §27.4.  akhil's `GC.Gen.MarkPhase.Minor`, for the page allocator:
/// the minor collection of `GC.Spec.Pages.Promote` at `mark_tal` (copies
/// black, free meaning blue) keeps
///
///   * the blocks in use, with their headers and major pointers, and what
///     they point at (`m_old_block`, `m_major_field`, `m_target`);
///   * nothing new is white: every new block is a black copy
///     (`m_new_black`);
///   * well-formedness for any admissible definition of free under which
///     the copies are in use (`m_wf_with`, akhil's `minor_keeps_wf_with`);
///   * the marking invariant, with the rewritten roots as outside
///     references (`m_keeps_marking_inv_with`, akhil's
///     `minor_keeps_marking_inv_with`);
///   * the account of the cycle (`m_account`, akhil's
///     `GC.Gen.MarkPhase.Completeness.account_minor`);
///   * and the page `Marking` invariant (`m_mark_inv`).
///
/// The proofs are akhil's, with his names, over the collection here: his
/// helpers private to `GC.Gen.MarkPhase.Minor` (`mem_of_index`,
/// `same_block_of_fields`, `update_agrees`, `free_unless_black`,
/// `rewritten_root`, `old_field_edge_at`, `keeps_marking_inv_with`) are
/// copied; `update_agrees` is stated for the allocator's free.

module GC.Spec.Pages.Promote.Mark

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Lib.Header
open GC.Spec.Fields
open GC.Gen.MinorHeap
open GC.Spec.Pages.Inv
open GC.Spec.Pages.Promote
open GC.Spec.Pages.Promote.Loop
open GC.Spec.Pages.Promote.Collect

module U64 = FStar.UInt64
module Promote = GC.Gen.Promote
module GenInv = GC.Gen.HeapInvariant
module MP = GC.Spec.MarkPhase
module MM = GC.Spec.MarkPhase.Mutator
module MPC = GC.Spec.MarkPhase.Completeness
module MCFH = GC.Gen.MinorCollectForwarding.Helpers
module GMM = GC.Gen.MarkPhase.Minor
module GMC = GC.Gen.MarkPhase.Completeness
module SPI = GC.Spec.SweepPhase.Intrinsic
module PUpd = GC.Gen.PromoteUpdate
module CV = GC.Gen.CheneyGeneric
module Mark = GC.Spec.Mark
module FT = GC.Spec.FieldTarget
module W = GC.Spec.Walk
module GB = GC.Gen.Base
module PMP = GC.Spec.Pages.MarkPhase
module PI = GC.Spec.Pages.PromoteInst

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10"

/// ---------------------------------------------------------------------------
/// The collection while marking
/// ---------------------------------------------------------------------------

/// **The minor collection while marking**, with the page allocator.
let mcollect (minor: minor_state) (g: heap) (st: pstate) (roots: seq U64.t) : GTot (gresult pstate) =
  collect PI.mark_tal minor g st roots

/// What it starts from: the page `Marking` invariant, the nursery's shape,
/// and its major pointers to blocks in use.
let mpre_mark (minor: minor_state) (g: heap) (st: pstate) : prop =
  PMP.mark_inv g st /\ GenInv.minor_heap_shape minor /\ GenInv.minor_major_fields_not_free free_stw minor g

let mpre_facts (minor: minor_state) (g: heap) (st: pstate)
  : Lemma (requires mpre_mark minor g st)
          (ensures cpre PI.mark_tal minor g st /\ well_formed_heap g /\ blocks_fit g /\ no_infix_block g /\
                   minor_wf minor /\ minor_infix_wf minor)
  = PI.mark_contract ();
    GenInv.minor_heap_shape_elim minor;
    contract_wf PI.mark_tal g st;
    wf_with_parts ()

/// The heap after.
let gm (minor: minor_state) (g: heap) (st: pstate) (roots: seq U64.t) : GTot heap =
  (mcollect minor g st roots).rmajor

/// **It keeps the page `Marking` invariant**, and well-formedness, and
/// empties the nursery.
let m_mark_inv (minor: minor_state) (g: heap) (st: pstate) (roots: seq U64.t)
  : Lemma (requires mpre_mark minor g st)
          (ensures (let r = mcollect minor g st roots in
                    PMP.mark_inv r.rmajor r.rst /\ well_formed_heap r.rmajor /\ r.rminor == minor_reset minor))
  = mpre_facts minor g st;
    collect_inv PI.mark_tal minor g st roots

/// ---------------------------------------------------------------------------
/// Blocks
/// ---------------------------------------------------------------------------

/// **Every block in use stays, with its header.**
let m_old_block (minor: minor_state) (g: heap) (st: pstate) (roots: seq U64.t) (y: obj_addr)
  : Lemma (requires mpre_mark minor g st /\ in_use free_stw g y)
          (ensures Seq.mem y (objects zero_addr (gm minor g st roots)) /\
                   read_word (gm minor g st roots) (hd_address y) == read_word g (hd_address y))
  = mpre_facts minor g st;
    collect_blocks PI.mark_tal minor g st roots y;
    free_stw_ok ();
    free_def_ok_elim free_stw

/// **Every new block is a black copy.**
let m_new_black (minor: minor_state) (g: heap) (st: pstate) (roots: seq U64.t) (y: obj_addr)
  : Lemma (requires mpre_mark minor g st /\ in_use free_stw (gm minor g st roots) y /\ ~(in_use free_stw g y))
          (ensures is_black y (gm minor g st roots))
  = mpre_facts minor g st;
    collect_blocks PI.mark_tal minor g st roots y;
    is_black_iff y (gm minor g st roots)

/// **A major pointer of a block in use stays.**
let m_major_field (minor: minor_state) (g: heap) (st: pstate) (roots: seq U64.t) (y: obj_addr) (j: nat)
  : Lemma (requires mpre_mark minor g st /\ in_use free_stw g y /\
                    j < U64.v (wosize_of_object y g) /\ U64.v y + j * 8 + 8 <= heap_size /\
                    is_pointer (read_word g (U64.uint_to_t (U64.v y + j * 8))))
          (ensures read_word (gm minor g st roots) (U64.uint_to_t (U64.v y + j * 8)) ==
                   read_word g (U64.uint_to_t (U64.v y + j * 8)))
  = mpre_facts minor g st;
    collect_major_field PI.mark_tal minor g st roots y j

/// **What a block in use stores keeps its resolution.**
let m_target (minor: minor_state) (g: heap) (st: pstate) (roots: seq U64.t) (w: U64.t)
  : Lemma (requires mpre_mark minor g st /\ is_pointer w /\ SPI.storable free_stw g w)
          (ensures resolve_object (w <: obj_addr) (gm minor g st roots) == resolve_object (w <: obj_addr) g)
  = mpre_facts minor g st;
    collect_target PI.mark_tal minor g st roots w

/// ---------------------------------------------------------------------------
/// Well-formedness for another definition of free
/// ---------------------------------------------------------------------------

/// Two blocks whose header and fields agree (akhil's).
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

/// The pointer update over the blocks in use for `free` and over those in
/// use for a smaller definition `un` agree on the blocks `un` keeps
/// (akhil's, with `free` for his `free_stw`).
#push-options "--z3rlimit 30"
let update_agrees (free: free_def) (pm: heap) (un: free_def) (fwd: Promote.forwarding_map) (x: obj_addr)
  : Lemma (requires blocks_fit pm /\ free_def_ok un /\ free_def_ok free /\
                    (forall (h: heap) (y: obj_addr). in_use un h y ==> in_use free h y) /\
                    in_use un (Promote.update_walk pm (in_use un pm) fwd) x)
          (ensures (let gS = Promote.update_walk pm (in_use un pm) fwd in
                    let g' = Promote.update_walk pm (in_use free pm) fwd in
                    SPI.same_block gS g' (hd_address x)))
  = let gS = Promote.update_walk pm (in_use un pm) fwd in
    let g' = Promote.update_walk pm (in_use free pm) fwd in
    free_def_ok_elim un;
    PUpd.update_walk_preserves_objects pm (in_use un pm) fwd;
    PUpd.update_walk_preserves_objects pm (in_use free pm) fwd;
    PUpd.update_walk_preserves_header pm (in_use un pm) fwd x;
    PUpd.update_walk_preserves_header pm (in_use free pm) fwd x;
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
            PUpd.update_walk_preserves_skipped_field pm (in_use free pm) fwd x j
          end else begin
            PUpd.update_walk_field_effect pm (in_use un pm) fwd x j;
            PUpd.update_walk_field_effect pm (in_use free pm) fwd x j
          end
        end
    in
    FStar.Classical.forall_intro fld;
    hd_address_spec x;
    same_block_of_fields gS g' x
#pop-options

/// **The heap after is well formed for any admissible definition of free**
/// under which the heap before was, the nursery's major pointers were in
/// use, every block in use is not blue, and the black copies are in use.
#push-options "--z3rlimit 30"
let m_wf_with (un: free_def) (minor: minor_state) (g: heap) (st: pstate) (roots: seq U64.t)
  : Lemma (requires mpre_mark minor g st /\ free_def_ok un /\ well_formed_heap_with un g /\
                    GenInv.minor_major_fields_not_free un minor g /\
                    (forall (h: heap) (y: obj_addr). in_use un h y ==> in_use free_stw h y) /\
                    copies_in_use PI.mark_tal un)
          (ensures well_formed_heap_with un (gm minor g st roots))
  = mpre_facts minor g st;
    promoted PI.mark_tal minor g st roots;
    collect_inv PI.mark_tal minor g st roots;
    let cs = promote PI.mark_tal minor g st roots in
    let pm = cs.major in
    let fwd = cs.fwd in
    let g' = gm minor g st roots in
    promoted_wf PI.mark_tal un minor g pm fwd;
    fwd_targets PI.mark_tal un minor g pm fwd;
    CV.update_pointers_with_preserves_wf un pm fwd;
    let gS = Promote.update_walk pm (in_use un pm) fwd in
    PUpd.update_walk_preserves_objects pm (in_use un pm) fwd;
    let iu (x: obj_addr) : Lemma (in_use un g' x == in_use un gS x) =
      if Seq.mem x (objects zero_addr pm) then begin
        PUpd.update_walk_preserves_header pm (in_use un pm) fwd x;
        in_use_is_determined_from_header un gS g' x
      end
    in
    FStar.Classical.forall_intro iu;
    free_stw_ok ();
    FStar.Classical.forall_intro (FStar.Classical.move_requires (update_agrees free_stw pm un fwd));
    wf_with_parts ();
    SPI.wf_transport gS g' un un
#pop-options

/// ---------------------------------------------------------------------------
/// Black objects' white targets: through `MP.unreached g` (akhil's)
/// ---------------------------------------------------------------------------

/// Every block in use for `un` is not blue.
let sub_stw (un: free_def) : prop = forall (h: heap) (y: obj_addr). in_use un h y ==> in_use free_stw h y

let unreached_sub (g0: heap) (sp: MP.scan_pos) : Lemma (sub_stw (MP.unreached g0 sp)) = ()

/// A black block is in use for `unreached`.
let unreached_copies (g0: heap) (sp: MP.scan_pos) : Lemma (copies_in_use PI.mark_tal (MP.unreached g0 sp))
  = let one (g: heap) (x: obj_addr)
      : Lemma (in_use free_stw g x /\ color_of_object x g == Black ==> in_use (MP.unreached g0 sp) g x)
      = is_black_iff x g; Mark.colors_exclusive x g
    in
    FStar.Classical.forall_intro_2 one

/// The nursery's fields point at blocks the marker will reach, if white.
#push-options "--z3rlimit 20"
let nursery_not_unreached (minor: minor_state) (g: heap) (st: pstate) (roots: seq U64.t) (sp: MP.scan_pos)
  : Lemma (requires mpre_mark minor g st /\ MP.marking_inv g (GMM.outside_refs_of minor g roots) sp)
          (ensures GenInv.minor_major_fields_not_free (MP.unreached g sp) minor g)
  = mpre_facts minor g st;
    let h (obj: U64.t) (j: nat)
      : Lemma (requires Seq.mem obj (minor_objects minor) /\ j < minor_scan_wosize minor obj /\
                        is_pointer_field (minor_read_field minor obj j))
              (ensures in_use (MP.unreached g sp) g (resolve_object ((minor_read_field minor obj j) <: obj_addr) g) /\
                       infix_addr_wf g (objects zero_addr g) ((minor_read_field minor obj j) <: obj_addr))
      = GenInv.minor_major_fields_not_free_elim free_stw minor g obj j;
        let v : obj_addr = minor_read_field minor obj j in
        let w : obj_addr = resolve_object v g in
        assert (GMM.nursery_refs minor g w);
        assert (GMM.outside_refs_of minor g roots w)
    in
    GenInv.minor_major_fields_not_free_intro (MP.unreached g sp) minor g h
#pop-options

/// **The heap after is well formed for `unreached g sp`.**
#push-options "--z3rlimit 20"
let unreached_wf_after (minor: minor_state) (g: heap) (st: pstate) (roots: seq U64.t) (sp: MP.scan_pos)
  : Lemma (requires mpre_mark minor g st /\ MP.marking_inv g (GMM.outside_refs_of minor g roots) sp)
          (ensures well_formed_heap_with (MP.unreached g sp) (gm minor g st roots))
  = MP.unreached_ok g sp;
    MP.marking_inv_unreached g (GMM.outside_refs_of minor g roots) sp;
    nursery_not_unreached minor g st roots sp;
    unreached_sub g sp;
    unreached_copies g sp;
    m_wf_with (MP.unreached g sp) minor g st roots
#pop-options

/// ---------------------------------------------------------------------------
/// The rewritten roots (akhil's)
/// ---------------------------------------------------------------------------

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

let black_copies (_: unit) : Lemma (copies_in_use PI.mark_tal free_unless_black)
  = let one (g: heap) (x: obj_addr)
      : Lemma (in_use free_stw g x /\ color_of_object x g == Black ==> in_use free_unless_black g x)
      = is_black_iff x g
    in
    FStar.Classical.forall_intro_2 one

let lt_arith (h p w wp: nat) : Lemma (requires p == h - w * 8 /\ h < p + wp * 8) (ensures w < wp) = ()

/// An infix target's closure facts, as the update's frame lemma asks.
#push-options "--z3rlimit 20"
let infix_parent_facts (pm: heap) (h: obj_addr)
  : Lemma (requires is_infix h pm /\ infix_addr_wf pm (objects zero_addr pm) h)
          (ensures (let w = U64.v (wosize_of_object h pm) in
                    let p = U64.v h - w * 8 in
                    w >= 2 /\ p >= 8 /\ p < heap_size /\ p % 8 == 0 /\
                    Seq.mem (U64.uint_to_t p <: obj_addr) (objects zero_addr pm) /\
                    w < U64.v (wosize_of_object (U64.uint_to_t p) pm)))
  = infix_addr_wf_elim pm (objects zero_addr pm) h;
    let w = U64.v (wosize_of_object h pm) in
    let p = U64.v h - w * 8 in
    lt_arith (U64.v h) p w (U64.v (wosize_of_object (U64.uint_to_t p) pm))
#pop-options

/// A white object a rewritten root points at was pointed at by an old root.
#push-options "--z3rlimit 40"
let rewritten_root (minor: minor_state) (g: heap) (st: pstate) (roots: seq U64.t) (r': U64.t) (w: obj_addr)
  : Lemma (requires mpre_mark minor g st /\ MCFH.roots_valid_for_minor_collection minor g roots /\
                    (let res = mcollect minor g st roots in
                     Seq.mem r' res.rroots /\ is_pointer r' /\
                     resolve_object (r' <: obj_addr) res.rmajor == w /\
                     Seq.mem w (objects zero_addr res.rmajor) /\
                     is_white w res.rmajor))
          (ensures GMM.root_refs g roots w)
  = let p = promote PI.mark_tal minor g st roots in
    let pm = p.major in
    let fwd = p.fwd in
    let res = mcollect minor g st roots in
    let g' = res.rmajor in
    mpre_facts minor g st;
    promoted PI.mark_tal minor g st roots;
    let i = FStar.Seq.Properties.index_mem r' res.rroots in
    Promote.rewrite_roots_index roots fwd i;
    let r = Seq.index roots i in
    mem_of_index roots i;
    GB.zero_addr_above_minor ();
    if Promote.is_minor_pointer r && fwd r <> 0UL then begin
      // a forwarded root: its target is a promoted copy, black
      let h : obj_addr = fwd r in
      free_unless_black_ok ();
      black_copies ();
      free_def_ok_elim free_unless_black;
      fwd_targets PI.mark_tal free_unless_black minor g pm fwd;
      let t = resolve_object h pm in
      (if is_infix h pm then begin
         infix_addr_wf_elim pm (objects zero_addr pm) h;
         infix_parent_facts pm h
       end else resolve_non_infix h pm);
      CV.update_walk_frame_target_header pm (in_use free_stw pm) fwd h;
      resolve_object_locality h pm g';
      PUpd.update_walk_preserves_header pm (in_use free_stw pm) fwd t;
      MM.header_kept_facts pm g' t;
      Mark.colors_exclusive t g'
    end else begin
      // an old root: it names the major block it resolves to
      assert (r == r');
      free_stw_ok ();
      m_target minor g st roots r
    end
#pop-options

/// ---------------------------------------------------------------------------
/// The collection keeps the marking invariant (akhil's)
/// ---------------------------------------------------------------------------

/// A field of a non-free block keeps its edge.
#push-options "--z3rlimit 20"
let old_field_edge_at (minor: minor_state) (g: heap) (st: pstate) (roots: seq U64.t)
  (s: obj_addr) (k: nat) (t: obj_addr)
  : Lemma (requires mpre_mark minor g st /\ in_use free_stw g s /\ MP.field_edge_at g s k t)
          (ensures MP.field_edge_at (gm minor g st roots) s k t)
  = let g' = gm minor g st roots in
    mpre_facts minor g st;
    free_stw_ok ();
    wf_with_parts ();
    m_old_block minor g st roots s;
    MM.header_kept_facts g g' s;
    m_mark_inv minor g st roots;
    MP.get_field_word g s k;
    MP.get_field_word g' s k;
    let w = read_word g (U64.uint_to_t (U64.v s + (k - 1) * 8)) in
    m_major_field minor g st roots s (k - 1);
    FT.wf_with_field free_stw g s (k - 1);
    m_target minor g st roots w
#pop-options

/// **The collection keeps the marking invariant**, with more outside
/// references `extra`, a fixed set of addresses: the program's roots and the
/// nursery's fields, or `extra`, before; the rewritten roots, or `extra`,
/// after (akhil's `keeps_marking_inv_with`).
#push-options "--z3rlimit 40"
let m_keeps_marking_inv_with (extra: obj_addr -> prop)
    (minor: minor_state) (g: heap) (st: pstate) (roots: seq U64.t) (sp: MP.scan_pos)
  : Lemma (requires mpre_mark minor g st /\
                    MCFH.roots_valid_for_minor_collection minor g roots /\
                    MP.marking_inv g (fun w -> GMM.outside_refs_of minor g roots w \/ extra w) sp)
          (ensures (let res = mcollect minor g st roots in
                    MP.marking_inv res.rmajor
                      (fun w -> GMM.root_refs res.rmajor res.rroots w \/ extra w) sp))
  =
  let outside_refs = fun w -> GMM.outside_refs_of minor g roots w \/ extra w in
  let res = mcollect minor g st roots in
  let g' = res.rmajor in
  let outside_refs' = fun w -> GMM.root_refs g' res.rroots w \/ extra w in
  assert (MP.marking_inv g (GMM.outside_refs_of minor g roots) sp);
  mpre_facts minor g st;
  m_mark_inv minor g st roots;
  free_stw_ok ();
  wf_with_parts ();
  // grey or white blocks stay, with their colours
  let gw (y: obj_addr)
    : Lemma (requires MP.grey_or_white g y)
            (ensures MP.grey_or_white g' y /\ (is_gray y g ==> is_gray y g'))
    = Mark.colors_exclusive y g;
      m_old_block minor g st roots y;
      MM.header_kept_facts g g' y
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires gw);
  // nothing new is white
  let wh (y: obj_addr)
    : Lemma (requires Seq.mem y (objects zero_addr g') /\ is_white y g')
            (ensures Seq.mem y (objects zero_addr g) /\ is_white y g)
    = Mark.colors_exclusive y g';
      if in_use free_stw g y then begin
        m_old_block minor g st roots y;
        MM.header_kept_facts g g' y
      end else m_new_black minor g st roots y
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires wh);
  // no edge out of a grey or white block is cut
  let cut (s t: obj_addr)
    : Lemma (requires MP.grey_or_white g s /\ MP.grey_or_white g t /\ MP.field_edge g s t)
            (ensures MP.field_edge g' s t)
    = Mark.colors_exclusive s g;
      m_old_block minor g st roots s;
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
              m_major_field minor g st roots s j;
              FT.wf_with_field free_stw g s j;
              m_target minor g st roots w
            end
          end
      in
      FStar.Classical.forall_intro fld;
      MM.field_edge_transfer g' g s (fun _ -> False) t
  in
  // ... and no unscanned one
  let cut_u (s t: obj_addr)
    : Lemma (requires MP.grey_or_white g s /\ MP.grey_or_white g t /\ MP.unscanned_edge g sp s t)
            (ensures MP.unscanned_edge g' sp s t)
    = cut s t;
      Mark.colors_exclusive s g;
      if s = sp.MP.cur then
        eliminate exists (k: nat). sp.MP.fld <= k /\ MP.field_edge_at g s k t
        with old_field_edge_at minor g st roots s k t
  in
  FStar.Classical.forall_intro_2 (fun s -> FStar.Classical.move_requires (cut_u s));
  // a scanned edge's white target is one the marker would reach
  unreached_wf_after minor g st roots sp;
  let blk (b t: obj_addr)
    : Lemma (requires MP.scanned_edge g' sp b t /\ is_white t g')
            (ensures MP.marker_will_reach g sp t)
    = if b = sp.MP.cur then gw b;
      assert (Seq.mem b (objects zero_addr g') /\ (is_black b g' \/ is_gray b g'));
      MP.scanned_edge_field_edge g' sp b t;
      MP.unreached_dark_edge g sp g' b t
  in
  FStar.Classical.forall_intro_2 (fun b -> FStar.Classical.move_requires (blk b));
  // a white object a rewritten root points at was an outside reference
  let hr (w: obj_addr)
    : Lemma (requires outside_refs' w /\ Seq.mem w (objects zero_addr g') /\ is_white w g')
            (ensures outside_refs w)
    = if FStar.IndefiniteDescription.strong_excluded_middle (extra w) then ()
      else
      eliminate exists (r': U64.t).
        Seq.mem r' res.rroots /\ is_pointer r' /\ resolve_object (r' <: obj_addr) g' == w
      with rewritten_root minor g st roots r' w
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires hr);
  MP.marking_inv_change g g' outside_refs outside_refs' sp
#pop-options

/// ---------------------------------------------------------------------------
/// The account (akhil's `account_minor`)
/// ---------------------------------------------------------------------------

/// Under `outside_snapshot`, every block in use is not blue, and a black one
/// is in use.
let snapshot_sub (snapshot: obj_addr -> prop)
  : Lemma (sub_stw (MPC.outside_snapshot snapshot) /\ copies_in_use PI.mark_tal (MPC.outside_snapshot snapshot))
  = let s1 (h: heap) (y: obj_addr)
      : Lemma (in_use (MPC.outside_snapshot snapshot) h y ==> in_use free_stw h y)
      = MPC.in_use_outside_snapshot snapshot h y
    in
    FStar.Classical.forall_intro_2 s1;
    let s2 (g: heap) (x: obj_addr)
      : Lemma (in_use free_stw g x /\ color_of_object x g == Black ==> in_use (MPC.outside_snapshot snapshot) g x)
      = MPC.in_use_outside_snapshot snapshot g x;
        is_black_iff x g;
        Mark.colors_exclusive x g
    in
    FStar.Classical.forall_intro_2 s2

/// **A minor collection while marking keeps the account**, with its
/// promoted copies added, when what the nursery holds is in the snapshot.
#push-options "--z3rlimit 30"
let m_account (snapshot: obj_addr -> prop) (minor: minor_state) (g: heap) (st: pstate) (roots: seq U64.t)
  : Lemma (requires mpre_mark minor g st /\ MPC.within_snapshot snapshot g /\
                    GenInv.minor_major_fields_not_free (MPC.outside_snapshot snapshot) minor g)
          (ensures (let g' = gm minor g st roots in
                    MPC.within_snapshot (GMC.with_new_blocks snapshot g g') g'))
  = let g' = gm minor g st roots in
    let snapshot' = GMC.with_new_blocks snapshot g g' in
    let un = MPC.outside_snapshot snapshot in
    MPC.outside_snapshot_ok snapshot;
    snapshot_sub snapshot;
    m_wf_with un minor g st roots;
    let iu (x: obj_addr) : Lemma (in_use (MPC.outside_snapshot snapshot') g' x == in_use un g' x) =
      if in_use free_stw g' x && not (in_use free_stw g x) then begin
        m_new_black minor g st roots x;
        Mark.colors_exclusive x g'
      end
    in
    FStar.Classical.forall_intro iu;
    SPI.well_formed_heap_with_congr un (MPC.outside_snapshot snapshot') g';
    let dk (y: obj_addr)
      : Lemma (requires Seq.mem y (objects zero_addr g') /\ (is_gray y g' \/ is_black y g'))
              (ensures snapshot' y)
      = Mark.colors_exclusive y g';
        if in_use free_stw g y then begin
          m_old_block minor g st roots y;
          MM.header_kept_facts g g' y
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires dk)
#pop-options
