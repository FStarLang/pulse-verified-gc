/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.AllocTagOk - what the page allocator with a tag guarantees
/// ---------------------------------------------------------------------------
///
/// Plan §27.1.  The tagged allocator (`GC.Spec.Pages.AllocTag.alloc_tag`)
/// is the coloured one with the new header written again, at its size and
/// colour (`Retag.rctx`).  So it meets, while marking and while sweeping,
/// what a minor collection needs of an allocation (`alloc_tag_marking`,
/// `alloc_tag_sweeping`): the new object, of the given wosize, tag and the
/// phase's colour, is the one block it brings into use; every other block in
/// use is kept; and once its fields are written (`AT.fields_written_away`)
/// the heap is in the phase's page invariant again.
///
/// The fill clause goes back to the untagged allocator's: for a scannable
/// object, the heap with the untagged header is one the untagged clause
/// covers (`field_back`); for a no-scan object, whose fields may hold
/// anything, the one with its fields cleared.  From there the retag and the
/// fill keep the invariant (`RetagInv.mc_chain`, `sw_chain`), and
/// well-formedness (`Retag.wf_retag`, `wf_fill_noscan`).
///
/// The pointer update of a minor collection rewrites fields of blocks in use
/// only, so it keeps the page invariant of both phases, given that the heap
/// it makes is well formed (`mark_inv_update`, `sw_update`).

module GC.Spec.Pages.AllocTagOk

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Walk
open GC.Spec.Pages.Shape
open GC.Spec.Pages.Inv
open GC.Spec.Pages.Retag

module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot
module F = GC.Spec.Pages.Fill
module Sc = GC.Spec.Pages.Scrub
module Rc = GC.Spec.Pages.Recolour
module CF = GC.Spec.Pages.ColourFacts
module R = GC.Spec.Pages.Replace
module B = GC.Spec.Pages.Blocks
module A = GC.Spec.Pages.Alloc
module AP = GC.Spec.Pages.AllocPhase
module PA = GC.Spec.Pages.Allocator
module PMP = GC.Spec.Pages.MarkPhase
module MS = GC.Spec.Pages.MidSweep
module MSA = GC.Spec.Pages.MidSweepAlloc
module NO = GC.Spec.Pages.NewOnly
module Th = GC.Spec.Pages.Theorems
module RI = GC.Spec.Pages.RetagInv
module CW = GC.Spec.Pages.FillFacts
module AT = GC.Spec.Pages.AllocTag
module I = GC.Spec.AllocIface
module Promote = GC.Gen.Promote
module Wf = GC.Spec.Pages.Wf

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// What counts as free reads the colour only
/// ---------------------------------------------------------------------------

let colour_free (free: free_def) : prop =
  forall (h h': heap) (y: obj_addr). color_of_object y h' == color_of_object y h ==> free h' y == free h y

let stw_colour () : Lemma (colour_free free_stw)
  = let aux (h h': heap) (y: obj_addr)
      : Lemma (color_of_object y h' == color_of_object y h ==> free_stw h' y == free_stw h y)
      = is_blue_iff y h; is_blue_iff y h'
    in
    FStar.Classical.forall_intro_3 aux

let sw_colour (pm: page_map) : Lemma (colour_free (MS.free_sw pm))
  = let aux (h h': heap) (y: obj_addr)
      : Lemma (color_of_object y h' == color_of_object y h ==> MS.free_sw pm h' y == MS.free_sw pm h y)
      = is_blue_iff y h; is_blue_iff y h'; is_white_iff y h; is_white_iff y h'
    in
    FStar.Classical.forall_intro_3 aux

/// The size and colour of `x` across a retag.
let r_x (g g': heap) (x: obj_addr)
  : Lemma (requires rctx g g' x)
          (ensures wosize_of_object x g' == wosize_of_object x g /\
                   color_of_object x g' == color_of_object x g)
  = R.hdr_obj g x; R.hdr_obj g' x;
    r_hdr g g' x (U64.v x - 8)

/// Blocks in use are the same across a retag, when free reads colours only.
let r_in_use (free: free_def) (g g': heap) (x: obj_addr)
  : Lemma (requires rctx g g' x /\ free_def_ok free /\ colour_free free)
          (ensures forall (y: obj_addr). in_use free g' y == in_use free g y)
  = r_objs g g' x;
    rctx_bframe g g' x;
    r_x g g' x;
    let aux (y: obj_addr) : Lemma (in_use free g' y == in_use free g y)
      = if y <> x then in_use_other free g g' x y
    in
    FStar.Classical.forall_intro aux

/// The tag facts of `x` follow its header word.
let tag_facts (g g': heap) (x: obj_addr)
  : Lemma (requires read_word g' (hd_address x) == read_word g (hd_address x))
          (ensures is_closure x g' == is_closure x g /\ is_infix x g' == is_infix x g /\
                   is_no_scan x g' == is_no_scan x g /\ tag_of_object x g' == tag_of_object x g)
  = resolve_object_locality x g g';
    is_no_scan_spec x g; is_no_scan_spec x g';
    tag_of_object_spec x g; tag_of_object_spec x g'

/// ---------------------------------------------------------------------------
/// The two ways back to the untagged allocator
/// ---------------------------------------------------------------------------

/// A scannable new object: put the untagged header back.
#push-options "--z3rlimit 40"
let scan_build (free: free_def) (g1 g2 g'': heap) (x: obj_addr)
  : Lemma (requires rctx g1 g2 x /\ free_def_ok free /\ colour_free free /\
                    ~(is_infix x g1) /\ ~(is_infix x g2) /\ ~(is_no_scan x g2) /\
                    AT.fields_written_away free g2 g'' x)
          (ensures (let g''1 = B.wr g'' (U64.v x - 8) (hdr g1 (U64.v x - 8)) in
                    I.fields_written_with free g1 g''1 x /\ rctx g''1 g'' x /\ F.fctx g'' g'' x /\
                    read_word g''1 (hd_address x) == read_word g1 (hd_address x) /\
                    read_word g'' (hd_address x) == read_word g2 (hd_address x)))
  = let h = U64.v x - 8 in
    let g''1 = B.wr g'' h (hdr g1 h) in
    hd_address_spec x;
    r_objs g1 g2 x;
    r_x g1 g2 x;
    assert (F.fctx g2 g'' x);
    F.obj_same g2 g'' x x;
    color_of_header_eq x g2 g'';
    is_blue_iff x g2; is_blue_iff x g'';
    let rd (a: hp_addr) : Lemma (read_word g''1 a == (if a = hd_address x then hdr g1 h else read_word g'' a))
      = B.wr_read g'' h (hdr g1 h) a
    in
    FStar.Classical.forall_intro rd;
    assert (mk_hp_addr h == hd_address x);
    r_hdr g1 g2 x h;
    assert (hdr g'' h == hdr g2 h);
    assert (rctx g'' g''1 x);
    r_objs g'' g''1 x;
    assert (rctx g''1 g'' x);
    tag_facts g2 g'' x;
    tag_facts g1 g''1 x;
    r_in_use free g'' g''1 x;
    r_x g'' g''1 x;
    wosize_of_object_spec x g2; wosize_of_object_spec x g'';
    let inside (a: hp_addr)
      : Lemma (requires U64.v x <= U64.v a /\ U64.v a < U64.v x + U64.v (wosize_of_object x g1) * 8)
              (ensures I.field_ok_with free g''1 (read_word g''1 a))
      = field_back free g'' g''1 x (read_word g'' a)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires inside)
#pop-options

/// A no-scan new object: clear its fields, and put the untagged header back.
#push-options "--z3rlimit 40"
let noscan_build (free: free_def) (g1 g2 g'': heap) (x: obj_addr)
  : Lemma (requires rctx g1 g2 x /\ AT.fields_written_away free g2 g'' x)
          (ensures (let h = U64.v x - 8 in
                    let gz = B.zeros g1 (U64.v x) (U64.v (wosize_of_object x g1)) in
                    let gt = B.wr gz h (hdr g2 h) in
                    I.fields_written_with free g1 gz x /\ rctx gz gt x /\ F.fctx gt g'' x /\
                    read_word gz (hd_address x) == read_word g1 (hd_address x) /\
                    read_word gt (hd_address x) == read_word g2 (hd_address x)))
  = let h = U64.v x - 8 in
    let n = U64.v (wosize_of_object x g1) in
    let gz = B.zeros g1 (U64.v x) n in
    let gt = B.wr gz h (hdr g2 h) in
    hd_address_spec x;
    assert (mk_hp_addr h == hd_address x);
    r_objs g1 g2 x;
    r_x g1 g2 x;
    r_hdr g1 g2 x h;
    let rz (a: hp_addr)
      : Lemma (read_word gz a == (if U64.v x <= U64.v a && U64.v a < U64.v x + n * 8 then 0UL else read_word g1 a))
      = B.zeros_read g1 (U64.v x) n a
    in
    FStar.Classical.forall_intro rz;
    let rt (a: hp_addr) : Lemma (read_word gt a == (if a = hd_address x then hdr g2 h else read_word gz a))
      = B.wr_read gz h (hdr g2 h) a
    in
    FStar.Classical.forall_intro rt;
    assert (F.fctx g1 gz x);
    F.obj_same g1 gz x x;
    color_of_header_eq x g1 gz;
    is_blue_iff x g1; is_blue_iff x gz;
    assert (rctx gz gt x);
    r_objs gz gt x;
    wosize_of_object_spec x gt; wosize_of_object_spec x g2;
    assert (F.fctx gt g'' x)
#pop-options

/// ---------------------------------------------------------------------------
/// The fill clauses
/// ---------------------------------------------------------------------------

/// **While marking.**
#push-options "--z3rlimit 40"
let fill_mark (g1 g2 g'': heap) (x: obj_addr) (st1: pstate)
  : Lemma (requires rctx g1 g2 x /\ ~(is_closure x g1) /\ ~(is_infix x g1) /\ ~(is_no_scan x g1) /\
                    ~(is_infix x g2) /\
                    (forall (h: heap). Th.fields_written g1 h x ==> PMP.mark_inv h st1) /\
                    AT.fields_written_away free_stw g2 g'' x)
          (ensures PMP.mark_inv g'' st1)
  = free_stw_ok ();
    stw_colour ();
    let h = U64.v x - 8 in
    if is_no_scan x g2 then begin
      let gz = B.zeros g1 (U64.v x) (U64.v (wosize_of_object x g1)) in
      let gt = B.wr gz h (hdr g2 h) in
      noscan_build free_stw g1 g2 g'' x;
      I.fields_written_stw g1 gz x;
      assert (PMP.mark_inv gz st1);
      tag_facts g1 gz x;
      tag_facts g2 gt x;
      r_x gz gt x;
      wf_retag free_stw gz gt x;
      wf_fill_noscan free_stw gt g'' x;
      RI.mc_chain gz gt g'' x st1
    end else begin
      let g''1 = B.wr g'' h (hdr g1 h) in
      scan_build free_stw g1 g2 g'' x;
      I.fields_written_stw g1 g''1 x;
      assert (PMP.mark_inv g''1 st1);
      tag_facts g1 g''1 x;
      tag_facts g2 g'' x;
      r_x g''1 g'' x;
      wf_retag free_stw g''1 g'' x;
      RI.mc_chain g''1 g'' g'' x st1
    end
#pop-options

/// **While sweeping.**
#push-options "--z3rlimit 40"
let fill_sweep (g1 g2 g'': heap) (x: obj_addr) (st st1: pstate)
  : Lemma (requires rctx g1 g2 x /\ ~(is_closure x g1) /\ ~(is_infix x g1) /\ ~(is_no_scan x g1) /\
                    ~(is_infix x g2) /\
                    (forall (y: obj_addr). MS.unswept_at st1.pm y == MS.unswept_at st.pm y) /\
                    (forall (h: heap). I.fields_written_with (MS.free_sw st.pm) g1 h x ==> MS.pages_ok_sw h st1) /\
                    AT.fields_written_away (MS.free_sw st1.pm) g2 g'' x)
          (ensures MS.pages_ok_sw g'' st1)
  = let fr = MS.free_sw st1.pm in
    MS.free_sw_ok st1.pm;
    sw_colour st1.pm;
    let same (h0: heap) (v: U64.t)
      : Lemma (I.field_ok_with fr h0 v ==> I.field_ok_with (MS.free_sw st.pm) h0 v)
      = ()
    in
    FStar.Classical.forall_intro_2 same;
    let h = U64.v x - 8 in
    if is_no_scan x g2 then begin
      let gz = B.zeros g1 (U64.v x) (U64.v (wosize_of_object x g1)) in
      let gt = B.wr gz h (hdr g2 h) in
      noscan_build fr g1 g2 g'' x;
      assert (I.fields_written_with (MS.free_sw st.pm) g1 gz x);
      assert (MS.pages_ok_sw gz st1);
      MS.pages_ok_sw_elim gz st1;
      tag_facts g1 gz x;
      tag_facts g2 gt x;
      r_x gz gt x;
      wf_retag fr gz gt x;
      wf_fill_noscan fr gt g'' x;
      RI.sw_chain gz gt g'' x st1
    end else begin
      let g''1 = B.wr g'' h (hdr g1 h) in
      scan_build fr g1 g2 g'' x;
      assert (I.fields_written_with (MS.free_sw st.pm) g1 g''1 x);
      assert (MS.pages_ok_sw g''1 st1);
      MS.pages_ok_sw_elim g''1 st1;
      tag_facts g1 g''1 x;
      tag_facts g2 g'' x;
      r_x g''1 g'' x;
      wf_retag fr g''1 g'' x;
      RI.sw_chain g''1 g'' g'' x st1
    end
#pop-options

/// ---------------------------------------------------------------------------
/// The new header
/// ---------------------------------------------------------------------------

/// The coloured allocator's new header has tag 0, so the object is neither
/// a closure, nor infix, nor no-scan; the tagged one rewrites it at the same
/// size and colour (`rctx`), with the tag asked for.
#push-options "--z3rlimit 40"
let new_hdr (col: color) (tag: AT.tag_t) (g: heap) (st: pstate) (wz: nat)
  : Lemma (requires col <> Blue /\ U64.v tag <> 249)
          (ensures (let (g1, st1, o) = AP.alloc_col col g st wz in
                    let (g2, st2, o2) = AT.alloc_col_tag col tag g st wz in
                    st2 == st1 /\ o2 == o /\ (o == 0UL ==> g2 == g1) /\
                    (o =!= 0UL /\ U64.v o >= 8 /\ U64.v o < heap_size /\ U64.v o % 8 == 0 ==>
                       (let x : obj_addr = o in
                        ~(is_closure x g1) /\ ~(is_infix x g1) /\ ~(is_no_scan x g1) /\
                        color_of_object x g1 == col /\
                        (Seq.mem x (objects zero_addr g1) ==>
                           rctx g1 g2 x /\ tag_of_object x g2 == tag /\ ~(is_infix x g2) /\
                           (is_no_scan x g2 <==> U64.v tag >= 251))))))
  = AT.alloc_col_tag_eq col tag g st wz;
    let (g', st', o) = A.alloc g st wz in
    if wz + 1 >= pow2 54 then ()
    else if o <> 0UL && U64.v o >= 8 && U64.v o < heap_size && U64.v o % 8 = 0 then begin
      let x : obj_addr = o in
      let h = U64.v x - 8 in
      hd_address_spec x;
      assert (mk_hp_addr h == hd_address x);
      A.alloc_clears g st wz;
      B.ohdr_spec wz;
      R.hdr_obj g' x;
      is_closure_spec x g'; is_infix_spec x g'; is_no_scan_spec x g';
      closure_tag_val (); infix_tag_val (); no_scan_tag_val ();
      AP.recolour_eq g' x col;
      color_change_preserves_is_closure x x g' col;
      color_change_preserves_is_infix x x g' col;
      color_preserves_is_no_scan x g' col;
      let g1 = AP.recolour g' o col in
      B.wr_read g' h (colorHeader (hdr g' h) col) (hd_address x);
      colorHeader_getColor (hdr g' h) col;
      color_of_object_spec x g1;
      assert (hdr g1 h == colorHeader (hdr g' h) col);
      let hd1 = hdr g1 h in
      let v = AT.tag_hdr hd1 col tag in
      let g2 = B.wr g1 h v in
      let rd (a: hp_addr) : Lemma (read_word g2 a == (if a = hd_address x then v else read_word g1 a))
        = B.wr_read g1 h v a
      in
      FStar.Classical.forall_intro rd;
      makeHeader_getWosize (getWosize hd1) col tag;
      makeHeader_getColor (getWosize hd1) col tag;
      makeHeader_getTag (getWosize hd1) col tag;
      assert (hdr g2 h == v);
      is_blue_iff x g1;
      tag_of_object_spec x g2;
      is_infix_spec x g2; is_no_scan_spec x g2
    end
#pop-options

/// A block not blue in `h` is not blue once whitened.
let not_blue_whiten (h: heap) (ys: list obj_addr) (y: obj_addr)
  : Lemma (requires ~(is_blue y h)) (ensures ~(is_blue y (Rc.whiten h ys)))
  = hd_address_spec y;
    Rc.paint_read h ys White (hd_address y);
    color_of_object_spec y h;
    color_of_object_spec y (Rc.whiten h ys);
    colorHeader_getColor (read_word h (hd_address y)) White;
    is_blue_iff y h;
    is_blue_iff y (Rc.whiten h ys)

/// **Only the new object comes into use while marking**, from the
/// invariant up to colours: `NO.alloc_new_only` on the whitened heap.
#push-options "--z3rlimit 40"
let mark_new_only (g: heap) (st: pstate) (wz: nat)
  : Lemma (requires AP.pages_ok_mc g st)
          (ensures (let (g1, _, o) = AP.alloc_col Black g st wz in NO.new_only g g1 o))
  = eliminate exists (ys: list obj_addr). CF.live_list g ys /\ pages_ok (Rc.whiten g ys) st
    with begin
      let (g', st', o) = A.alloc g st wz in
      let gw = Rc.whiten g ys in
      AP.base g ys st wz;
      NO.alloc_new_only gw st wz;
      if o = 0UL then begin
        AP.zero_case g ys st wz;
        NO.new_only_refl g o
      end else begin
        AP.new_facts g ys st wz Black;
        let x : obj_addr = o in
        R.hdr_obj g' x;
        R.hdr_obj (Rc.whiten g' ys) x;
        is_blue_iff x g';
        CF.step_facts g' x Black;
        let one (y: obj_addr)
          : Lemma (requires Seq.mem y (objects zero_addr g') /\ ~(is_blue y g') /\ U64.v y <> U64.v o)
                  (ensures Seq.mem y (objects zero_addr g) /\ ~(is_blue y g))
          = not_blue_whiten g' ys y
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires one)
      end
    end
#pop-options

/// Every block in use other than `x` is kept, header and body.
#push-options "--z3rlimit 30"
let others_tag (g g1 g2: heap) (x: obj_addr)
  : Lemma (requires Th.others_unchanged g g1 /\ rctx g1 g2 x /\
                    ~(Seq.mem x (objects zero_addr g) /\ ~(is_blue x g)))
          (ensures I.others_unchanged g g2)
  = rctx_bframe g1 g2 x;
    r_objs g1 g2 x;
    let one (y: obj_addr)
      : Lemma (requires Seq.mem y (objects zero_addr g) /\ ~(is_blue y g))
              (ensures Seq.mem y (objects zero_addr g2) /\
                       read_word g2 (hd_address y) == read_word g (hd_address y) /\
                       (forall (b: hp_addr). U64.v y <= U64.v b /\ U64.v b < U64.v y + U64.v (wosize_of_object y g) * 8 ==>
                          read_word g2 b == read_word g b))
      = src_kept g1 g2 x y y;
        wosize_of_object_spec y g; wosize_of_object_spec y g1;
        hd_address_spec x;
        let b1 (b: hp_addr)
          : Lemma (U64.v y <= U64.v b /\ U64.v b < U64.v y + U64.v (wosize_of_object y g) * 8 ==>
                   read_word g2 b == read_word g b)
          = if U64.v y <= U64.v b && U64.v b < U64.v y + U64.v (wosize_of_object y g) * 8 then
              other_away g1 x y (U64.v b)
        in
        FStar.Classical.forall_intro b1
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires one)
#pop-options

/// ---------------------------------------------------------------------------
/// The allocator with a tag, while marking and while sweeping
/// ---------------------------------------------------------------------------

/// **While marking**: black, the one block it brings into use, and the
/// `Marking` page invariant once the fields are written.
#push-options "--z3rlimit 40"
let alloc_tag_marking (g: heap) (st: pstate) (wz: nat) (tag: AT.tag_t)
  : Lemma (requires PMP.mark_inv g st /\ U64.v tag <> 249)
          (ensures (let (g', st', o) = AT.alloc_tag I.Marking g st wz tag in
                    PMP.all_swept st' /\
                    (o == 0UL ==> g' == g /\ st' == st) /\
                    (o =!= 0UL ==>
                       U64.v o >= 8 /\ U64.v o < heap_size /\ U64.v o % 8 == 0 /\
                       (let x : obj_addr = o in
                        U64.v x + wz * 8 <= heap_size /\
                        Seq.mem x (objects zero_addr g') /\
                        U64.v (wosize_of_object x g') == wz /\
                        tag_of_object x g' == tag /\
                        is_black x g' /\
                        ~(Seq.mem x (objects zero_addr g) /\ ~(is_blue x g)) /\
                        (forall (y: obj_addr). in_use free_stw g' y == (in_use free_stw g y || y = x)) /\
                        (forall (g'': heap). AT.fields_written_away free_stw g' g'' x ==> PMP.mark_inv g'' st')) /\
                       I.others_unchanged g g')))
  = assert_norm (I.new_colour I.Marking == Black);
    PMP.mark_inv_alloc g st wz;
    new_hdr Black tag g st wz;
    mark_new_only g st wz;
    let (g1, st1, o) = AP.alloc_col Black g st wz in
    let (g2, st2, o2) = AT.alloc_tag I.Marking g st wz tag in
    if o <> 0UL then begin
      let x : obj_addr = o in
      r_objs g1 g2 x;
      r_x g1 g2 x;
      R.obj_iff g2 x;
      R.hdr_obj g2 x;
      is_black_iff x g2;
      let iu (y: obj_addr) : Lemma (in_use free_stw g2 y == (in_use free_stw g y || y = x))
        = if y <> x && Seq.mem y (objects zero_addr g) && not (is_blue y g) then
            color_of_header_eq y g g1
      in
      FStar.Classical.forall_intro iu;
      let fill (g'': heap) : Lemma (AT.fields_written_away free_stw g2 g'' x ==> PMP.mark_inv g'' st1)
        = if FStar.IndefiniteDescription.strong_excluded_middle (AT.fields_written_away free_stw g2 g'' x)
          then fill_mark g1 g2 g'' x st1
      in
      FStar.Classical.forall_intro fill;
      others_tag g g1 g2 x
    end
#pop-options

/// **While sweeping**: white, in a swept page, the one block it brings into
/// use, and the mid-sweep invariant once the fields are written.
#push-options "--z3rlimit 40"
let alloc_tag_sweeping (g: heap) (st: pstate) (wz: nat) (tag: AT.tag_t)
  : Lemma (requires MS.pages_ok_sw g st /\ U64.v tag <> 249)
          (ensures (let (g', st', o) = AT.alloc_tag I.Sweeping g st wz tag in
                    (forall (y: obj_addr). MS.unswept_at st'.pm y == MS.unswept_at st.pm y) /\
                    (o == 0UL ==> g' == g /\ st' == st) /\
                    (o =!= 0UL ==>
                       U64.v o >= 8 /\ U64.v o < heap_size /\ U64.v o % 8 == 0 /\
                       (let x : obj_addr = o in
                        U64.v x + wz * 8 <= heap_size /\
                        Seq.mem x (objects zero_addr g') /\
                        U64.v (wosize_of_object x g') == wz /\
                        tag_of_object x g' == tag /\
                        is_white x g' /\ not (MS.unswept_at st.pm x) /\
                        ~(Seq.mem x (objects zero_addr g) /\ ~(is_blue x g)) /\
                        (forall (y: obj_addr). in_use (MS.free_sw st'.pm) g' y == (in_use (MS.free_sw st.pm) g y || y = x)) /\
                        (forall (g'': heap). AT.fields_written_away (MS.free_sw st'.pm) g' g'' x ==> MS.pages_ok_sw g'' st')) /\
                       I.others_unchanged g g')))
  = assert_norm (I.new_colour I.Sweeping == White);
    MSA.alloc_sw_ok g st wz;
    new_hdr White tag g st wz;
    let (g1, st1, o) = AP.alloc_col White g st wz in
    let (g2, st2, o2) = AT.alloc_tag I.Sweeping g st wz tag in
    let us (y: obj_addr) : Lemma (MS.unswept_at st1.pm y == MS.unswept_at st.pm y)
      = MS.uw_same st.pm st1.pm (U64.v y - 8)
    in
    FStar.Classical.forall_intro us;
    if o <> 0UL then begin
      let x : obj_addr = o in
      r_objs g1 g2 x;
      r_x g1 g2 x;
      R.obj_iff g2 x;
      R.hdr_obj g2 x;
      is_white_iff x g1; is_white_iff x g2;
      MS.free_sw_ok st1.pm;
      sw_colour st1.pm;
      r_in_use (MS.free_sw st1.pm) g1 g2 x;
      let fill (g'': heap) : Lemma (AT.fields_written_away (MS.free_sw st1.pm) g2 g'' x ==> MS.pages_ok_sw g'' st1)
        = if FStar.IndefiniteDescription.strong_excluded_middle (AT.fields_written_away (MS.free_sw st1.pm) g2 g'' x)
          then fill_sweep g1 g2 g'' x st st1
      in
      FStar.Classical.forall_intro fill;
      others_tag g g1 g2 x
    end
#pop-options

/// ---------------------------------------------------------------------------
/// The pointer update keeps the page invariants
/// ---------------------------------------------------------------------------

/// Rewriting the fields of `obj` from field `i` on changes no other word.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 30"
let rec uop_frame (major: heap) (obj: U64.t) (wz: nat) (fwd: Promote.forwarding_map) (i: nat) (a: hp_addr)
  : Lemma (requires U64.v obj % 8 == 0 /\ (U64.v a < U64.v obj + i * 8 \/ U64.v a >= U64.v obj + wz * 8))
          (ensures read_word (Promote.update_object_pointers major obj wz fwd i) a == read_word major a)
          (decreases (wz - i))
  = if i >= wz then ()
    else begin
      let fo = U64.v obj + i * 8 in
      if fo + 8 > heap_size || fo % 8 <> 0 then ()
      else begin
        let fa : hp_addr = U64.uint_to_t fo in
        let fv = GC.Gen.Base.to_minor_offset (read_word major fa) in
        if Promote.is_minor_pointer fv then begin
          let nv = fwd fv in
          if nv <> 0UL then begin
            read_write_different major fa a nv;
            uop_frame (write_word major fa nv) obj wz fwd (i + 1) a
          end else uop_frame major obj wz fwd (i + 1) a
        end else uop_frame major obj wz fwd (i + 1) a
      end
    end
#pop-options

/// `h` has the objects of `g`, with their headers.
let same_hd (g h: heap) : prop =
  (forall (y: obj_addr). Seq.mem y (objects zero_addr h) <==> Seq.mem y (objects zero_addr g)) /\
  (forall (y: obj_addr). Seq.mem y (objects zero_addr g) ==> read_word h (hd_address y) == read_word g (hd_address y))

let live_same (g h: heap) (ys: list obj_addr)
  : Lemma (requires same_hd g h /\ CF.live_list g ys) (ensures CF.live_list h ys)
  = let one (y: obj_addr) : Lemma (requires L.mem y ys) (ensures Seq.mem y (objects zero_addr h) /\ ~(is_blue y h))
      = color_of_header_eq y g h; is_blue_iff y g; is_blue_iff y h
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires one)

/// One object's fields rewritten: the objects, headers and core (of the
/// heap with `ys` whitened) are kept; with nothing whitened, so is "no grey
/// block in an unswept page".
#push-options "--z3rlimit 40"
let step_keeps (g: heap) (st: pstate) (ys: list obj_addr) (h h': heap) (obj: obj_addr)
  : Lemma (requires CF.live_list g ys /\ same_hd g h /\ Sc.core (Rc.whiten h ys) st /\
                    (ys == [] ==> MS.no_grey_unswept h st.pm) /\
                    Seq.mem obj (objects zero_addr g) /\ ~(is_blue obj g) /\
                    (forall (a: hp_addr). U64.v a < U64.v obj \/ U64.v a >= F.fields_end h obj ==>
                       read_word h' a == read_word h a))
          (ensures same_hd g h' /\ Sc.core (Rc.whiten h' ys) st /\ (ys == [] ==> MS.no_grey_unswept h' st.pm))
  = color_of_header_eq obj g h; is_blue_iff obj g; is_blue_iff obj h;
    assert (F.fctx h h' obj);
    FStar.Classical.forall_intro (FStar.Classical.move_requires (F.obj_same h h' obj));
    live_same g h ys;
    RI.w_fctx h h' obj ys;
    not_blue_whiten h ys obj;
    Sc.core_fill (Rc.whiten h ys) (Rc.whiten h' ys) obj st;
    if FStar.IndefiniteDescription.strong_excluded_middle (ys == []) then begin
      Rc.whiten_nil h;
      CW.no_grey_fill h h' obj st
    end
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
let rec walk_keeps (g: heap) (st: pstate) (ys: list obj_addr)
    (upd: obj_addr -> GTot bool) (fwd: Promote.forwarding_map) (h: heap) (idx: nat)
  : Lemma (requires Promote.walk_ok g upd /\ CF.live_list g ys /\ same_hd g h /\
                    Sc.core (Rc.whiten h ys) st /\ (ys == [] ==> MS.no_grey_unswept h st.pm))
          (ensures (let h' = Promote.update_walk_aux h (objects zero_addr g) upd fwd idx in
                    same_hd g h' /\ Sc.core (Rc.whiten h' ys) st /\ (ys == [] ==> MS.no_grey_unswept h' st.pm)))
          (decreases (Seq.length (objects zero_addr g) - idx))
  = let objs = objects zero_addr g in
    if idx >= Seq.length objs then ()
    else begin
      let obj = Seq.index objs idx in
      if not (upd obj) then walk_keeps g st ys upd fwd h (idx + 1)
      else if is_no_scan obj h then walk_keeps g st ys upd fwd h (idx + 1)
      else begin
        let wz = U64.v (wosize_of_object obj h) in
        let h' = Promote.update_object_pointers h obj wz fwd 0 in
        FStar.Classical.forall_intro (FStar.Classical.move_requires (uop_frame h obj wz fwd 0));
        step_keeps g st ys h h' obj;
        walk_keeps g st ys upd fwd h' (idx + 1)
      end
    end
#pop-options

/// **While marking.**
#push-options "--z3rlimit 30"
let mark_inv_update (g: heap) (st: pstate) (upd: obj_addr -> GTot bool) (fwd: Promote.forwarding_map)
  : Lemma (requires PMP.mark_inv g st /\ Promote.walk_ok g upd /\
                    well_formed_heap (Promote.update_walk g upd fwd))
          (ensures PMP.mark_inv (Promote.update_walk g upd fwd) st)
  = let g' = Promote.update_walk g upd fwd in
    eliminate exists (ys: list obj_addr). CF.live_list g ys /\ pages_ok (Rc.whiten g ys) st
    with begin
      Sc.core_of_ok (Rc.whiten g ys) st;
      walk_keeps g st ys upd fwd g 0;
      live_same g g' ys;
      CF.whiten_facts g' ys;
      Wf.wfh_old_parts ();
      Sc.ok_of_core (Rc.whiten g' ys) st
    end
#pop-options

/// **While sweeping.**
#push-options "--z3rlimit 30"
let sw_update (g: heap) (st: pstate) (upd: obj_addr -> GTot bool) (fwd: Promote.forwarding_map)
  : Lemma (requires MS.pages_ok_sw g st /\ Promote.walk_ok g upd /\
                    well_formed_heap_with (MS.free_sw st.pm) (Promote.update_walk g upd fwd))
          (ensures MS.pages_ok_sw (Promote.update_walk g upd fwd) st)
  = let g' = Promote.update_walk g upd fwd in
    MS.pages_ok_sw_elim g st;
    AP.live_list_nil g;
    Rc.whiten_nil g;
    Rc.whiten_nil g';
    walk_keeps g st [] upd fwd g 0;
    MS.pages_ok_sw_intro g' st
#pop-options
