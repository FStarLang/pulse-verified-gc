/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar2.Witness — a concrete heap with a cycle, meeting
/// `mark_pre`
///
/// The Stage 1 witness g2 (`GC.Spec.MarkPar.Witness`) with B's field set to
/// A:
///
///     A  at zero_addr + 8:   wosize 2, tag 0, white; fields [B; 0]
///     B  at zero_addr + 32:  wosize 1, tag 0, white; field  [A]
///
/// and every later word zero (white wosize-0 objects).  The pointer from B
/// back to A, a lower address, is what lets a fix-up walk find a white child
/// below its position.  `g5_pre_roots` proves `mark_pre g5 roots` for any
/// roots among A and B.
/// ---------------------------------------------------------------------------
module GC.Spec.MarkPar2.Witness

open FStar.Seq
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Spec.MarkPar.Model
open GC.Spec.MarkPar.Witness

module HeapGraph = GC.Spec.HeapGraph
module Mark = GC.Spec.Mark

let g5 (_: squash big) : heap = write_word g2 (obj_B ()) vA

#push-options "--z3rlimit 20"
let read_g5 (_: squash big) (a: hp_addr)
  : Lemma (read_word (g5 ()) a ==
           (if a = zero_addr then hA
            else if a = vA then vB
            else if U64.v a = za + 24 then hB
            else if a = obj_B () then vA
            else 0UL))
  = let b = obj_B () in
    read_write_same g2 b vA;
    if a = b then ()
    else begin
      assert (U64.v a % 8 == 0 /\ U64.v b % 8 == 0);
      read_write_different g2 b a vA;
      read_g2 () a
    end
#pop-options

/// g5 and g2 agree on every header word.
let headers_g5 (_: squash big) (a: hp_addr)
  : Lemma (requires a <> obj_B ()) (ensures read_word (g5 ()) a == read_word g2 a)
  = read_g5 () a; read_g2 () a

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let objects_g5 (_: squash big)
  : Lemma (let b = obj_B () in
           let p40 : hp_addr = U64.uint_to_t (za + 40) in
           objects zero_addr (g5 ()) == Seq.cons vA (Seq.cons b (objects p40 (g5 ()))) /\
           Seq.mem vA (objects zero_addr (g5 ())) /\ Seq.mem b (objects zero_addr (g5 ())) /\
           hd_address b == hd_B () /\
           (forall (x: obj_addr). Seq.mem x (objects p40 (g5 ())) ==> U64.v (hd_address x) >= za + 40) /\
           (forall (x: obj_addr). Seq.mem x (objects zero_addr (g5 ())) ==>
              x == vA \/ x == b \/ U64.v (hd_address x) >= za + 40))
  = let g = g5 () in
    let b = obj_B () in
    hd_address_spec b;
    hA_facts ();
    read_g5 () zero_addr;
    let p24 = hd_B () in
    let p40 : hp_addr = U64.uint_to_t (za + 40) in
    read_g5 () p24;
    f_address_spec zero_addr;
    f_address_spec p24;
    assert (objects zero_addr g == Seq.cons vA (objects p24 g));
    assert (objects p24 g == Seq.cons b (objects p40 g));
    Seq.mem_cons vA (objects p24 g);
    Seq.mem_cons b (objects p40 g);
    let tail (x: obj_addr) : Lemma (requires Seq.mem x (objects p40 g)) (ensures U64.v (hd_address x) >= za + 40) =
      hd_address_spec x; objects_above p40 g x in
    FStar.Classical.forall_intro (FStar.Classical.move_requires tail);
    let rest (x: obj_addr)
      : Lemma (requires Seq.mem x (objects zero_addr g))
              (ensures x == vA \/ x == b \/ U64.v (hd_address x) >= za + 40)
      = hd_address_spec x;
        if x = vA then ()
        else if x = b then ()
        else objects_above p40 g x
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires rest)
#pop-options

let header_g5 (_: squash big) (x: obj_addr)
  : Lemma (requires Seq.mem x (objects zero_addr (g5 ())))
          (ensures read_word (g5 ()) (hd_address x) ==
                   (if x = vA then hA else if x = obj_B () then hB else 0UL))
  = objects_g5 ();
    hd_address_spec x;
    hd_address_spec (obj_B ());
    read_g5 () (hd_address x)

let facts_g5 (_: squash big) (x: obj_addr)
  : Lemma (requires Seq.mem x (objects zero_addr (g5 ())))
          (ensures wosize_of_object x (g5 ()) ==
                     (if x = vA then 2UL else if x = obj_B () then 1UL else 0UL) /\
                   tag_of_object x (g5 ()) == 0UL /\
                   color_of_object x (g5 ()) == White /\
                   is_white x (g5 ()) /\ ~(is_gray x (g5 ())) /\ ~(is_black x (g5 ())) /\
                   ~(is_blue x (g5 ())) /\ ~(is_infix x (g5 ())) /\ ~(is_no_scan x (g5 ())))
  = let g = g5 () in
    header_g5 () x;
    hA_facts (); zero_header ();
    wosize_of_object_spec x g;
    tag_of_object_spec x g;
    color_of_object_spec x g;
    is_white_iff x g; is_gray_iff x g; is_black_iff x g; is_blue_iff x g;
    is_infix_spec x g; is_no_scan_spec x g;
    infix_tag_val (); no_scan_tag_val ()

let fields_g5 (_: squash big)
  : Lemma (let b = obj_B () in
           HeapGraph.get_field (g5 ()) vA 1UL == vB /\ HeapGraph.get_field (g5 ()) vA 2UL == 0UL /\
           HeapGraph.get_field (g5 ()) b 1UL == vA /\
           HeapGraph.is_pointer_field vB /\ HeapGraph.is_pointer_field vA /\
           ~(HeapGraph.is_pointer_field 0UL))
  = let b = obj_B () in
    hd_address_spec vA; hd_address_spec b;
    read_g5 () vA;
    read_g5 () (U64.uint_to_t (za + 16));
    read_g5 () (U64.uint_to_t (za + 32));
    fields_g2 ()

/// The pointer fields: A's first, to B, and B's, to A.
#push-options "--z3rlimit 40 --fuel 3 --ifuel 1"
let efp_g5 (_: squash big) (x dst: obj_addr)
  : Lemma (requires Seq.mem x (objects zero_addr (g5 ())) /\
                    U64.v (wosize_of_object x (g5 ())) < pow2 54 /\
                    exists_field_pointing_to_unchecked (g5 ()) x (wosize_of_object x (g5 ())) dst)
          (ensures (x == vA /\ dst == obj_B ()) \/ (x == obj_B () /\ dst == vA))
  = let g = g5 () in
    facts_g5 () x;
    let b = obj_B () in
    hd_address_spec b;
    hd_address_spec dst;
    hd_address_spec vA;
    fields_g5 ();
    if x = vA then begin
      read_g5 () vA;
      read_g5 () (U64.uint_to_t (za + 16));
      assert (U64.add_mod vA (U64.mul_mod 1UL mword) == U64.uint_to_t (za + 16));
      assert (U64.add_mod vA (U64.mul_mod 0UL mword) == vA)
    end else if x = b then begin
      read_g5 () b;
      assert (U64.add_mod b (U64.mul_mod 0UL mword) == b)
    end
#pop-options

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let wf_g5 (_: squash big)
  : Lemma (well_formed_heap (g5 ()))
  = let g = g5 () in
    let b = obj_B () in
    objects_g5 ();
    facts_g5 () b; facts_g5 () vA;
    resolve_non_infix b g;
    resolve_non_infix vA g;
    let p1 (x: obj_addr) : Lemma (requires Seq.mem x (objects zero_addr g))
        (ensures U64.v (hd_address x) + 8 + (U64.v (wosize_of_object x g) * 8) <= Seq.length g) =
      facts_g5 () x; hd_address_spec x in
    FStar.Classical.forall_intro (FStar.Classical.move_requires p1);
    let p4 (x: obj_addr) : Lemma (requires Seq.mem x (objects zero_addr g)) (ensures ~(is_infix x g)) =
      facts_g5 () x in
    FStar.Classical.forall_intro (FStar.Classical.move_requires p4);
    let p2 (src dst: obj_addr)
      : Lemma (requires Seq.mem src (objects zero_addr g) /\ fields_constrained g src /\
                        (let wz = wosize_of_object src g in
                         U64.v wz < pow2 54 /\ exists_field_pointing_to_unchecked g src wz dst))
              (ensures Seq.mem (resolve_object dst g) (objects zero_addr g))
      = efp_g5 () src dst
    in
    well_formed_heap_part2_intro g p2;
    let p3 (src dst: obj_addr)
      : Lemma (requires Seq.mem src (objects zero_addr g) /\ fields_constrained g src /\
                        (let wz = wosize_of_object src g in
                         U64.v wz < pow2 54 /\ exists_field_pointing_to_unchecked g src wz dst))
              (ensures infix_addr_wf g (objects zero_addr g) dst)
      = efp_g5 () src dst;
        infix_addr_wf_intro g (objects zero_addr g) dst
    in
    well_formed_heap_part3_intro g p3;
    reveal_opaque (`%well_formed_heap) well_formed_heap
#pop-options

/// The precondition, met, for any roots among A and B.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let g5_pre_roots (_: squash big) (roots: list obj_addr)
  : Lemma (requires forall (r: obj_addr). L.memP r roots ==> r == vA \/ r == obj_B ())
          (ensures mark_pre (g5 ()) roots)
  = let g = g5 () in
    wf_g5 ();
    objects_g5 ();
    let b = obj_B () in
    facts_g5 () vA; facts_g5 () b;
    resolve_non_infix vA g;
    resolve_non_infix b g;
    let col (x: obj_addr) : Lemma (requires Seq.mem x (objects zero_addr g))
        (ensures ~(is_gray x g) /\ ~(is_black x g)) = facts_g5 () x in
    FStar.Classical.forall_intro (FStar.Classical.move_requires col);
    let npb (src dst: obj_addr)
      : Lemma (requires Seq.mem src (objects zero_addr g) /\ ~(is_blue src g) /\
                        fields_constrained g src /\ points_to g src dst)
              (ensures ~(is_blue (resolve_object dst g) g))
      = wosize_of_object_bound src g;
        efp_g5 () src dst
    in
    FStar.Classical.forall_intro_2 (fun src dst -> FStar.Classical.move_requires (npb src) dst);
    assert (Mark.no_pointer_to_blue g);
    assert (Mark.noGreyObjects g);
    assert (Mark.no_black_objects g)
#pop-options
