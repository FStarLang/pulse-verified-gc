module GC.Spec.SweepPhase.Util

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FusedSweep
open GC.Spec.FusedSweep.Inv

module U64 = FStar.UInt64
module Header = GC.Lib.Header
module W = GC.Spec.Walk
module FL = GC.Spec.FreeList
module FLA = GC.Spec.FreeList.Ascending

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

#push-options "--z3rlimit 40"
let header_eta (h: U64.t)
  : Lemma (makeHeader (getWosize h) (getColor h) (getTag h) == h)
  = makeHeader_is_pack_header64 (getWosize h) (getColor h) (getTag h);
    all_headers_valid h;
    Header.unpack_pack_header (U64.v h);
    getWosize_spec h; getTag_spec h; getColor_spec h;
    Header.mask_tag_value ();
    Header.get_tag_bound (U64.v h);
    Header.get_wosize_bound (U64.v h);
    assert (U64.v (getWosize h) == Header.get_wosize (U64.v h));
    assert (U64.v (getTag h) == Header.get_tag (U64.v h))
#pop-options

let header_eq h h' = header_eta h; header_eta h'

let part1_holds g =
  let aux (h: obj_addr)
    : Lemma (requires Seq.mem h (objects zero_addr g))
            (ensures (let wz = wosize_of_object h g in
                      U64.v (hd_address h) + 8 + (U64.v wz * 8) <= Seq.length g))
    = W.objects_mem_iff g zero_addr h;
      W.hd_address_pos h;
      wosize_of_object_spec h g
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

/// ---------------------------------------------------------------------------
/// The walk
/// ---------------------------------------------------------------------------

let no_pos_inside g p q = W.reaches_block_before g zero_addr p q

#push-options "--z3rlimit 40"
let seg_replace g g' a b =
  W.reaches_bounds g a b;
  let below (x: nat)
    : Lemma (requires x <= U64.v a)
            (ensures W.reaches g' zero_addr x <==> W.reaches g zero_addr x)
    = W.reaches_frame_below g g' zero_addr x
  in
  below (U64.v a);
  W.reaches_trans g' zero_addr a b;
  W.reaches_trans g zero_addr a b;
  let above (x: nat)
    : Lemma (requires x >= b)
            (ensures W.reaches g' zero_addr x <==> W.reaches g zero_addr x)
    = if b >= heap_size then begin
        (if W.reaches g zero_addr x then W.reaches_bounds g zero_addr x);
        (if W.reaches g' zero_addr x then W.reaches_bounds g' zero_addr x)
      end else begin
        let bb = mk_hp_addr b in
        W.walk_frame_from g g' bb;
        (if W.reaches g zero_addr x then begin
           W.reaches_det g zero_addr bb x;
           W.reaches_trans g' zero_addr bb x
         end);
        (if W.reaches g' zero_addr x then begin
           W.reaches_det g' zero_addr bb x;
           W.reaches_trans g zero_addr bb x
         end)
      end
  in
  let inside (x: nat)
    : Lemma (requires U64.v a <= x /\ x <= b)
            (ensures W.reaches g' zero_addr x <==> W.reaches g' a x)
    = (if W.reaches g' zero_addr x then W.reaches_det g' zero_addr a x);
      (if W.reaches g' a x then W.reaches_trans g' zero_addr a x)
  in
  let one (x: nat)
    : Lemma ((x <= U64.v a \/ x >= b) ==> (W.reaches g' zero_addr x <==> W.reaches g zero_addr x))
    = if x <= U64.v a then below x else if x >= b then above x
  in
  FStar.Classical.forall_intro one;
  FStar.Classical.forall_intro (FStar.Classical.move_requires inside)
#pop-options

#push-options "--z3rlimit 30"
let write_off_walk g a v
  = W.walk_write g zero_addr a v;
    let hd (q: hp_addr)
      : Lemma (requires W.reaches g zero_addr (U64.v q))
              (ensures read_word (write_word g a v) q == read_word g q)
      = read_write_different g a q v
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires hd)
#pop-options

#push-options "--z3rlimit 30"
let cells_transfer g g'
  = let aux (x: U64.t) : Lemma (FL.fl_cell g' x <==> FL.fl_cell g x)
      = fl_cell_iff g x; fl_cell_iff g' x;
        if is_obj x && U64.v x >= U64.v zero_addr + 8 then begin
          let q = mk_hp_addr (U64.v x - 8) in
          if W.reaches g zero_addr (U64.v q) then assert (read_word g' q == read_word g q)
        end
    in
    FStar.Classical.forall_intro aux
#pop-options

#push-options "--fuel 1"
let dead_run_first (g1: heap) (a: hp_addr) (b: nat)
  : Lemma (requires dead_run g1 a b /\ U64.v a < b)
          (ensures W.can_step g1 a /\ not (black_at g1 a) /\ W.bnext g1 a <= b)
  = ()
#pop-options

let swept_block_kinds g1 g p =
  W.bnext_facts g p;
  white_header_facts (read_word g1 p);
  if black_at g1 p then begin
    if not (marked_block g1 g p) then dead_run_first g1 p (W.bnext g p)
  end
  else dead_run_first g1 p (W.bnext g p)

#push-options "--z3rlimit 40"
let rec behind_pos_ref_aux (g1 g: heap) (c: nat) (p: nat)
  : Lemma (requires W.reaches g zero_addr c /\ behind_ok g1 g c /\
                    W.reaches g zero_addr p /\ p <= c)
          (ensures W.reaches g1 zero_addr p)
          (decreases p)
  = W.reaches_bounds g zero_addr p;
    if p = U64.v zero_addr then W.reaches_refl g1 zero_addr
    else begin
      let q = W.last_block g zero_addr p in
      behind_ok_elim g1 g c q;
      swept_block_kinds g1 g q;
      behind_pos_ref_aux g1 g c (U64.v q);
      if black_at g1 q then W.reaches_snoc g1 zero_addr q
      else begin
        dead_run_reaches g1 q p;
        W.reaches_trans g1 zero_addr q p
      end
    end
#pop-options

let behind_pos_ref g1 g c p = behind_pos_ref_aux g1 g c p

#push-options "--z3rlimit 30"
let front_pos g1 g c p
  = W.reaches_bounds g zero_addr c;
    front_same_elim g1 g c p;
    let ca = mk_hp_addr c in
    let fr (w: hp_addr) : Lemma (requires U64.v w >= U64.v ca) (ensures read_word g w == read_word g1 w)
      = front_same_elim g1 g c w in
    FStar.Classical.forall_intro (FStar.Classical.move_requires fr);
    W.walk_frame_from g1 g ca;
    if W.reaches g zero_addr (U64.v p) then begin
      W.reaches_det g zero_addr ca (U64.v p);
      W.reaches_trans g1 zero_addr ca (U64.v p)
    end;
    if W.reaches g1 zero_addr (U64.v p) then begin
      W.reaches_det g1 zero_addr ca (U64.v p);
      W.reaches_trans g zero_addr ca (U64.v p)
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Blackening a set of blocks
/// ---------------------------------------------------------------------------

let black_header_facts h =
  makeHeader_getWosize (getWosize h) Header.Black (getTag h);
  makeHeader_getColor (getWosize h) Header.Black (getTag h);
  makeHeader_getTag (getWosize h) Header.Black (getTag h)

#push-options "--fuel 1 --z3rlimit 20"
let rec recolour_read_aux (sel: hp_addr -> GTot bool) (g: heap) (p: hp_addr) (a: hp_addr)
  : Lemma (ensures read_word (recolour sel g p) a ==
                   (if W.reaches g p (U64.v a) && W.can_step g a && sel a
                    then black_header (read_word g a) else read_word g a))
          (decreases (heap_size - U64.v p))
  = if not (W.can_step g p) then begin
      if W.reaches g p (U64.v a) then begin
        W.reaches_bounds g p (U64.v a);
        if U64.v p < U64.v a then W.reaches_unfold g p (U64.v a)
      end
    end else begin
      let hb = black_header (read_word g p) in
      let g1 = if sel p then write_word g p hb else g in
      let n = W.bnext g p in
      W.bnext_facts g p;
      let same (w: hp_addr) : Lemma (requires w <> p) (ensures read_word g1 w == read_word g w)
        = if sel p then read_write_different g p w hb
      in
      (if sel p then read_write_same g p hb);
      if U64.v a < U64.v p then begin
        if W.reaches g p (U64.v a) then W.reaches_bounds g p (U64.v a)
      end;
      if U64.v a > U64.v p && W.reaches g p (U64.v a) then W.reaches_unfold g p (U64.v a);
      if n >= heap_size then begin
        if U64.v a <> U64.v p then same a
      end else begin
        let nn = mk_hp_addr n in
        recolour_read_aux sel g1 nn a;
        let fr (w: hp_addr) : Lemma (requires U64.v w >= U64.v nn) (ensures read_word g1 w == read_word g w)
          = same w in
        FStar.Classical.forall_intro (FStar.Classical.move_requires fr);
        W.walk_frame_from g g1 nn;
        if U64.v a < n && W.reaches g1 nn (U64.v a) then W.reaches_bounds g1 nn (U64.v a);
        if U64.v a <> U64.v p then begin
          same a;
          if U64.v a > U64.v p then begin
            W.reaches_refl g nn;
            if W.reaches g nn (U64.v a) then begin
              W.reaches_step g p;
              W.reaches_trans g p nn (U64.v a)
            end
          end
        end
      end
    end
#pop-options

let recolour_read sel g p a = recolour_read_aux sel g p a
