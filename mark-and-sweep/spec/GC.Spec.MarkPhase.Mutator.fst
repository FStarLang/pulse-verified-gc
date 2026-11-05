module GC.Spec.MarkPhase.Mutator

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Graph.Within
open GC.Spec.MarkPhase

module U64 = FStar.UInt64
module SPI = GC.Spec.SweepPhase.Intrinsic
module SPM = GC.Spec.SweepPhase.Mutator
module Mark = GC.Spec.Mark
module FT = GC.Spec.FieldTarget
module Header = GC.Lib.Header

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10"

/// ---------------------------------------------------------------------------
/// Headers and edges
/// ---------------------------------------------------------------------------

/// Everything read off a header is the same when the header is.
let header_kept_facts (g g': heap) (y: obj_addr)
  : Lemma (requires read_word g' (hd_address y) == read_word g (hd_address y))
          (ensures (is_black y g' <==> is_black y g) /\ (is_white y g' <==> is_white y g) /\
                   (is_gray y g' <==> is_gray y g) /\ (is_blue y g' <==> is_blue y g) /\
                   is_no_scan y g' == is_no_scan y g /\ is_closure y g' == is_closure y g /\
                   wosize_of_object y g' == wosize_of_object y g)
  = color_of_object_spec y g; color_of_object_spec y g';
    is_black_iff y g; is_black_iff y g';
    is_white_iff y g; is_white_iff y g';
    is_gray_iff y g; is_gray_iff y g';
    is_blue_iff y g; is_blue_iff y g';
    is_no_scan_spec y g; is_no_scan_spec y g';
    tag_of_object_spec y g; tag_of_object_spec y g';
    resolve_object_locality y g g'

/// An edge of `s` in `g'` is one in `g`, or ends where `q` holds, when every
/// pointer field of `s` in `g'` is the same in `g` (with the same resolution)
/// or resolves where `q` holds.
#push-options "--z3rlimit 20"
let field_edge_transfer (g g': heap) (s: obj_addr) (q: obj_addr -> prop) (t: obj_addr)
  : Lemma (requires blocks_fit g /\ blocks_fit g' /\
                    Seq.mem s (objects zero_addr g) /\ Seq.mem s (objects zero_addr g') /\
                    read_word g' (hd_address s) == read_word g (hd_address s) /\
                    field_edge g' s t /\
                    (~(is_no_scan s g) ==>
                     (forall (j: nat). j < U64.v (wosize_of_object s g) /\ U64.v s + j * 8 + 8 <= heap_size ==>
                       (let w = read_word g' (U64.uint_to_t (U64.v s + j * 8)) in
                        is_pointer w ==>
                        (read_word g (U64.uint_to_t (U64.v s + j * 8)) == w /\
                         resolve_object (w <: obj_addr) g == resolve_object (w <: obj_addr) g') \/
                        q (resolve_object (w <: obj_addr) g')))))
          (ensures field_edge g s t \/ q t)
  = header_kept_facts g g' s;
    eliminate exists (c: obj_addr). points_to g' s c /\ resolve_object c g' == t
    with begin
      let p (d: obj_addr) : prop =
        (points_to g s d /\ resolve_object d g == resolve_object d g') \/ q (resolve_object d g')
      in
      let field (j: nat)
        : Lemma (requires j < U64.v (wosize_of_object s g') /\ U64.v s + j * 8 + 8 <= heap_size)
                (ensures (let w = read_word g' (U64.uint_to_t (U64.v s + j * 8)) in
                          is_pointer w ==> p (w <: obj_addr)))
        = let fa = U64.uint_to_t (U64.v s + j * 8) in
          let w = read_word g' fa in
          if is_pointer w && read_word g fa = w then
            FT.field_pointer_points_to_nat g s (w <: obj_addr) j
      in
      pointer_from_field g' s c p field
    end
#pop-options

/// ---------------------------------------------------------------------------
/// What a write changes
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20"
let target_header_away g x a w =
  let ww : obj_addr = w in
  SPM.in_body_block g x a;
  SPI.colour_of g x;
  SPI.body_word g (hd_address x) a;
  hd_address_spec ww;
  (if is_infix ww g then begin
     infix_addr_wf_elim g (objects zero_addr g) ww;
     let p : obj_addr = U64.uint_to_t (U64.v ww - U64.v (wosize_of_object ww g) * 8) in
     assert (SPM.in_body g p (hd_address ww));
     SPM.in_body_block g p (hd_address ww);
     SPM.other_body g x p a
   end else begin
     resolve_non_infix ww g;
     SPI.obj_pos g ww
   end);
  let rs (v: U64.t) : Lemma (resolve_object ww (write_word g a v) == resolve_object ww g) =
    read_write_different g a (hd_address ww) v;
    resolve_object_locality ww g (write_word g a v)
  in
  FStar.Classical.forall_intro rs
#pop-options

let write_heads g x a v =
  let g' = write_word g a v in
  SPM.in_body_block g x a;
  SPI.colour_of g x;
  SPI.body_write g 0UL (hd_address x) a v;
  SPI.same_heads_facts g g';
  let f (y: obj_addr)
    : Lemma (Seq.mem y (objects zero_addr g) ==>
             (is_black y g' <==> is_black y g) /\ (is_white y g' <==> is_white y g) /\
             (is_gray y g' <==> is_gray y g) /\ (is_blue y g' <==> is_blue y g) /\
             is_no_scan y g' == is_no_scan y g /\ is_closure y g' == is_closure y g)
    = if Seq.mem y (objects zero_addr g) then header_kept_facts g g' y
  in
  FStar.Classical.forall_intro f

#push-options "--z3rlimit 30"
let write_wf g x a v =
  let g' = write_word g a v in
  let free = free_stw in
  write_heads g x a v;
  SPI.same_heads_facts g g';
  free_stw_ok ();
  free_def_ok_elim free;
  wf_with_parts ();
  SPM.same_heads_part4 g g';
  GC.Spec.SweepPhase.Util.part1_holds g';
  // the non-free objects keep their headers, and closures their blocks
  let kept (y: obj_addr)
    : Lemma (requires in_use free g y)
            (ensures read_word g' (hd_address y) == read_word g (hd_address y) /\
                     (is_closure y g ==> SPI.same_block g g' (hd_address y)))
    = if is_closure y g then begin
        SPM.other_body g x y a;
        SPI.obj_pos g y;
        let body (b: hp_addr)
          : Lemma (requires U64.v (hd_address y) < U64.v b /\ U64.v b < GC.Spec.Walk.bnext g (hd_address y))
                  (ensures read_word g' b == read_word g b)
          = read_write_different g a b v
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires body)
      end
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires kept);
  assert (SPI.heads_kept free g g');
  let closure (src: obj_addr) (j: nat)
    : Lemma (requires in_use free g' src /\ ~(is_no_scan src g') /\
                      j < U64.v (wosize_of_object src g') /\ U64.v src + j * 8 + 8 <= heap_size)
            (ensures (let w = read_word g' (U64.uint_to_t (U64.v src + j * 8)) in
                      is_pointer w ==>
                      in_use free g' (resolve_object (w <: obj_addr) g') /\
                      infix_addr_wf g' (objects zero_addr g') (w <: obj_addr)))
    = let b : hp_addr = U64.uint_to_t (U64.v src + j * 8) in
      let w = read_word g' b in
      SPI.colour_of g src; SPI.colour_of g' src;
      is_no_scan_spec src g; is_no_scan_spec src g';
      if b = a then begin
        read_write_same g a v;
        (if src <> x then begin
           assert (SPM.in_body g' src b);
           SPM.in_body_block g' src b;
           SPM.other_body g x src a
         end);
        SPI.storable_transfer g g' free free v
      end else begin
        read_write_different g a b v;
        if is_pointer w then begin
          FT.wf_with_field free g src j;
          SPI.storable_transfer g g' free free w
        end
      end
  in
  pointer_clauses_from_field_closure free g' closure
#pop-options

/// A field of a block other than `x` is not the written word.
let other_field (g: heap) (x u: obj_addr) (a: hp_addr) (j: nat)
  : Lemma (requires Seq.mem x (objects zero_addr g) /\ Seq.mem u (objects zero_addr g) /\ u <> x /\
                    SPM.in_body g x a /\
                    j < U64.v (wosize_of_object u g) /\ U64.v u + j * 8 + 8 <= heap_size)
          (ensures U64.uint_to_t (U64.v u + j * 8) <> a)
  = let fa : hp_addr = U64.uint_to_t (U64.v u + j * 8) in
    SPM.in_body_block g u fa;
    SPM.other_body g x u a

/// A pointer field of a non-free, scannable block is storable.
let field_storable (g: heap) (s: obj_addr) (j: nat)
  : Lemma (requires well_formed_heap g /\ in_use free_stw g s /\ ~(is_no_scan s g) /\
                    j < U64.v (wosize_of_object s g) /\ U64.v s + j * 8 + 8 <= heap_size)
          (ensures SPI.storable free_stw g (read_word g (U64.uint_to_t (U64.v s + j * 8))))
  = free_stw_ok ();
    if is_pointer (read_word g (U64.uint_to_t (U64.v s + j * 8))) then FT.wf_with_field free_stw g s j

#push-options "--z3rlimit 20"
let write_edges_other g x a v u t =
  let g' = write_word g a v in
  write_heads g x a v;
  wf_with_parts ();
  GC.Spec.SweepPhase.Util.part1_holds g';
  header_kept_facts g g' u;
  let fld (h: heap) (j: nat)
    : Lemma (requires h == g \/ h == g')
            (ensures j < U64.v (wosize_of_object u g) /\ U64.v u + j * 8 + 8 <= heap_size /\ ~(is_no_scan u g) ==>
                     (let fa = U64.uint_to_t (U64.v u + j * 8) in
                      let w = read_word h fa in
                      is_pointer w ==>
                      read_word g fa == w /\ read_word g' fa == w /\
                      resolve_object (w <: obj_addr) g == resolve_object (w <: obj_addr) g'))
    = if j < U64.v (wosize_of_object u g) && U64.v u + j * 8 + 8 <= heap_size && not (is_no_scan u g) then begin
        let fa : hp_addr = U64.uint_to_t (U64.v u + j * 8) in
        other_field g x u a j;
        read_write_different g a fa v;
        field_storable g u j;
        let w = read_word g fa in
        if is_pointer w then target_header_away g x a w
      end
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires (fld g));
  FStar.Classical.forall_intro (FStar.Classical.move_requires (fld g'));
  FStar.Classical.move_requires (field_edge_transfer g g' u (fun _ -> False)) t;
  FStar.Classical.move_requires (field_edge_transfer g' g u (fun _ -> False)) t
#pop-options

#push-options "--z3rlimit 20"
let write_edges_new g x a v t =
  let g' = write_word g a v in
  write_heads g x a v;
  wf_with_parts ();
  GC.Spec.SweepPhase.Util.part1_holds g';
  header_kept_facts g g' x;
  let q (t': obj_addr) : prop = value_target g v t' in
  let fld (j: nat)
    : Lemma (j < U64.v (wosize_of_object x g) /\ U64.v x + j * 8 + 8 <= heap_size /\ ~(is_no_scan x g) ==>
             (let fa = U64.uint_to_t (U64.v x + j * 8) in
              let w = read_word g' fa in
              is_pointer w ==>
              (read_word g fa == w /\ resolve_object (w <: obj_addr) g == resolve_object (w <: obj_addr) g') \/
              q (resolve_object (w <: obj_addr) g')))
    = if j < U64.v (wosize_of_object x g) && U64.v x + j * 8 + 8 <= heap_size && not (is_no_scan x g) then begin
        let fa : hp_addr = U64.uint_to_t (U64.v x + j * 8) in
        if fa = a then begin
          read_write_same g a v;
          if is_pointer v then target_header_away g x a v
        end else begin
          read_write_different g a fa v;
          field_storable g x j;
          let w = read_word g fa in
          if is_pointer w then target_header_away g x a w
        end
      end
  in
  FStar.Classical.forall_intro fld;
  field_edge_transfer g g' x q t
#pop-options

#push-options "--z3rlimit 20"
let write_edges_old g x a v t =
  let g' = write_word g a v in
  write_heads g x a v;
  wf_with_parts ();
  GC.Spec.SweepPhase.Util.part1_holds g';
  header_kept_facts g g' x;
  let old = read_word g a in
  let q (t': obj_addr) : prop = value_target g old t' in
  let fld (j: nat)
    : Lemma (j < U64.v (wosize_of_object x g') /\ U64.v x + j * 8 + 8 <= heap_size /\ ~(is_no_scan x g') ==>
             (let fa = U64.uint_to_t (U64.v x + j * 8) in
              let w = read_word g fa in
              is_pointer w ==>
              (read_word g' fa == w /\ resolve_object (w <: obj_addr) g' == resolve_object (w <: obj_addr) g) \/
              q (resolve_object (w <: obj_addr) g)))
    = if j < U64.v (wosize_of_object x g') && U64.v x + j * 8 + 8 <= heap_size && not (is_no_scan x g') then begin
        let fa : hp_addr = U64.uint_to_t (U64.v x + j * 8) in
        if fa = a then ()
        else begin
          read_write_different g a fa v;
          field_storable g x j;
          let w = read_word g fa in
          if is_pointer w then target_header_away g x a w
        end
      end
  in
  FStar.Classical.forall_intro fld;
  field_edge_transfer g' g x q t
#pop-options

/// ---------------------------------------------------------------------------
/// The write
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 30"
let marking_write g held x a v =
  let g' = write_word g a v in
  write_heads g x a v;
  write_wf g x a v;
  free_stw_ok ();
  let cut (s t: obj_addr)
    : Lemma (requires grey_or_white g s /\ grey_or_white g t /\ field_edge g s t)
            (ensures field_edge g' s t \/ is_gray t g')
    = Mark.colors_exclusive s g;
      Mark.colors_exclusive t g;
      if s = x then write_edges_old g x a v t
      else write_edges_other g x a v s t
  in
  FStar.Classical.forall_intro_2 (fun s -> FStar.Classical.move_requires (cut s));
  let black (b t: obj_addr)
    : Lemma (requires Seq.mem b (objects zero_addr g') /\ is_black b g' /\ field_edge g' b t /\ is_white t g')
            (ensures (Seq.mem b (objects zero_addr g) /\ is_black b g /\ field_edge g b t) \/
                     marker_will_reach g t)
    = Mark.colors_exclusive b g;
      if b = x then begin
        write_edges_new g x a v t;
        if FStar.IndefiniteDescription.strong_excluded_middle (field_edge g x t) then ()
        else begin
          // t is the new value's target: a non-free block, white before too
          assert (SPI.storable free_stw g v);
          free_def_ok_elim free_stw;
          assert (Seq.mem t (objects zero_addr g))
        end
      end else write_edges_other g x a v b t
  in
  FStar.Classical.forall_intro_2 (fun b -> FStar.Classical.move_requires (black b));
  marking_inv_change g g' held held
#pop-options

let marking_write_immediate g held x a v = marking_write g held x a v

/// ---------------------------------------------------------------------------
/// The deletion barrier
/// ---------------------------------------------------------------------------

let darken_inv g held w =
  if is_pointer w &&
     Seq.mem (resolve_object (w <: obj_addr) g) (objects zero_addr g) &&
     is_white (resolve_object (w <: obj_addr) g) g
  then marking_inv_grey g held (resolve_object (w <: obj_addr) g)

/// The index of the field at a body word.
let slot_index (g: heap) (x: obj_addr) (a: hp_addr)
  : Ghost nat (requires SPM.in_body g x a)
              (ensures fun j -> U64.v x + j * 8 == U64.v a /\ j < U64.v (wosize_of_object x g) /\
                             U64.v x + j * 8 + 8 <= heap_size)
  = FStar.Math.Lemmas.lemma_div_exact (U64.v a - U64.v x) 8;
    (U64.v a - U64.v x) / 8

/// Greying a white block `t0` keeps what the write needs.
#push-options "--z3rlimit 30"
let grey_keeps_write (g: heap) (held: obj_addr -> prop) (t0 x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires marking_inv g held /\ Seq.mem t0 (objects zero_addr g) /\ is_white t0 g /\
                    SPM.program_write free_stw g x a v /\
                    (~(is_no_scan x g) ==> target_ok g held v))
          (ensures (let g1 = makeGray t0 g in
                    SPM.program_write free_stw g1 x a v /\
                    is_no_scan x g1 == is_no_scan x g /\
                    (~(is_no_scan x g) ==> target_ok g1 held v)))
  = let g1 = makeGray t0 g in
    makeGray_eq t0 g;
    makeGray_is_gray t0 g;
    color_change_preserves_objects g t0 Header.Gray;
    Mark.colors_exclusive t0 g1;
    let col (y: obj_addr)
      : Lemma (y <> t0 ==> ((is_black y g1 <==> is_black y g) /\ (is_white y g1 <==> is_white y g) /\
                            (is_gray y g1 <==> is_gray y g) /\ (is_blue y g1 <==> is_blue y g)))
      = if y <> t0 then begin
          color_change_preserves_other_color t0 y g Header.Gray;
          is_black_iff y g; is_black_iff y g1; is_white_iff y g; is_white_iff y g1;
          is_gray_iff y g; is_gray_iff y g1; is_blue_iff y g; is_blue_iff y g1
        end
    in
    FStar.Classical.forall_intro col;
    color_change_preserves_wosize_any t0 x g Header.Gray;
    color_change_preserves_is_closure t0 x g Header.Gray;
    (if x = t0 then color_preserves_is_no_scan x g Header.Gray
     else color_change_preserves_other_is_no_scan t0 x g Header.Gray);
    if is_pointer v then begin
      let vv : obj_addr = v in
      color_change_preserves_resolve t0 vv g Header.Gray;
      color_change_preserves_is_infix t0 vv g Header.Gray;
      color_change_preserves_wosize_any t0 vv g Header.Gray;
      let cl (o: obj_addr)
        : Lemma (is_closure o g1 == is_closure o g /\ wosize_of_object o g1 == wosize_of_object o g)
        = color_change_preserves_is_closure t0 o g Header.Gray;
          color_change_preserves_wosize_any t0 o g Header.Gray
      in
      FStar.Classical.forall_intro cl;
      (if not (is_no_scan x g) then
         infix_addr_wf_congr g g1 (objects zero_addr g) vv);
      let t = resolve_object vv g in
      if FStar.IndefiniteDescription.strong_excluded_middle (marker_will_reach g t) then
        marker_will_reach_grey g t0 t
    end
#pop-options

#push-options "--z3rlimit 30"
let marking_write_barrier g held x a v =
  let old = read_word g a in
  let g1 = darken g old in
  darken_inv g held old;
  if is_pointer old &&
     Seq.mem (resolve_object (old <: obj_addr) g) (objects zero_addr g) &&
     is_white (resolve_object (old <: obj_addr) g) g
  then begin
    let t0 = resolve_object (old <: obj_addr) g in
    grey_keeps_write g held t0 x a v;
    makeGray_eq t0 g;
    makeGray_is_gray t0 g;
    Mark.colors_exclusive t0 g1;
    color_change_preserves_resolve t0 (old <: obj_addr) g Header.Gray;
    // the written word is not t0's header: it is a body word of x
    SPM.in_body_block g x a;
    SPI.colour_of g x;
    SPI.body_word g (hd_address x) a;
    SPI.obj_pos g t0;
    color_change_preserves_other_read t0 a g Header.Gray;
    assert (read_word g1 a == old);
    marking_write g1 held x a v
  end else begin
    // nothing to darken: the old value's target, if any, is not white
    (if not (is_no_scan x g) && is_pointer old then begin
       let j = slot_index g x a in
       field_storable g x j;
       free_stw_ok ();
       free_def_ok_elim free_stw
     end);
    marking_write g held x a v
  end
#pop-options

/// ---------------------------------------------------------------------------
/// Loads
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20"
let marking_load g held s t =
  let held' (w: obj_addr) : prop = held w \/ w == t in
  let r (w: obj_addr)
    : Lemma (requires held' w /\ Seq.mem w (objects zero_addr g) /\ is_white w g)
            (ensures marker_will_reach g w)
    = if FStar.IndefiniteDescription.strong_excluded_middle (held w) then ()
      else begin
        Mark.color_exhaustive s g;
        Mark.colors_exclusive s g;
        assert (grey_or_white g t);
        if is_gray s g then begin
          reach_within_edge (field_edge g) (grey_or_white g) s t
        end else if is_white s g then begin
          eliminate exists (x: obj_addr). is_gray x g /\ reach_within (field_edge g) (grey_or_white g) x s
          with begin
            reach_within_edge (field_edge g) (grey_or_white g) s t;
            reach_within_trans (field_edge g) (grey_or_white g) x s t
          end
        end
      end
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires r);
  assert (held_reached g held')
#pop-options
