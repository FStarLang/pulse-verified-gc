/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar.Witness — a concrete heap that meets `mark_pre`
///
/// The vacuity checks (`GC.Spec.MarkPar.Vacuity`) need arguments that meet
/// each lemma's precondition.  This module builds them: the all-zero heap
/// with two objects written into it,
///
///     A  at zero_addr + 8:   wosize 2, tag 0, white; fields [B; 0]
///     B  at zero_addr + 32:  wosize 1, tag 0, white; field  [0]
///
/// and every word after them zero, which reads as further wosize-0 white
/// objects.  A has two fields so that a scan can be part-way through it,
/// and B has one so that two workers can be scanning at once.  `heap_size` is abstract, so everything here assumes the heap
/// has room for A and B (`big`).  `g2_pre` proves `mark_pre g2 [A]`.
/// ---------------------------------------------------------------------------
module GC.Spec.MarkPar.Witness

open FStar.Seq
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module U32 = FStar.UInt32
module Header = GC.Lib.Header
module Seq = FStar.Seq
module L = FStar.List.Tot

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Spec.MarkPar.Model

module HeapGraph = GC.Spec.HeapGraph
module Mark = GC.Spec.Mark

let za : nat = U64.v zero_addr

let big : prop = za + 48 <= heap_size

/// ---------------------------------------------------------------------------
/// The zero heap
/// ---------------------------------------------------------------------------

let z : heap = Seq.create heap_size 0uy

let shr0 (k: U32.t{U32.v k < 64}) : Lemma (U64.shift_right 0UL k == 0UL /\ uint64_to_uint8 0UL == 0uy)
  = FStar.UInt.shift_right_value_lemma #64 0 (U32.v k)

let combine_zero () : Lemma (combine_bytes 0uy 0uy 0uy 0uy 0uy 0uy 0uy 0uy == 0UL)
  = shr0 8ul; shr0 16ul; shr0 24ul; shr0 32ul; shr0 40ul; shr0 48ul; shr0 56ul;
    combine_decompose_identity 0UL

let index_zero (i: nat{i < heap_size}) : Lemma (Seq.index z i == 0uy)
  = Seq.lemma_index_create heap_size 0uy i

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let read_zero (a: hp_addr) : Lemma (read_word z a == 0UL)
  = let n = U64.v a in
    read_word_spec z a;
    index_zero n; index_zero (n + 1); index_zero (n + 2); index_zero (n + 3);
    index_zero (n + 4); index_zero (n + 5); index_zero (n + 6); index_zero (n + 7);
    combine_zero ()
#pop-options

let and0 (m: FStar.UInt.uint_t 64) : Lemma (FStar.UInt.logand #64 0 m == 0)
  = FStar.UInt.logand_commutative #64 0 m; FStar.UInt.logand_lemma_1 #64 m

let zero_header ()
  : Lemma (getWosize 0UL == 0UL /\ getTag 0UL == 0UL /\ getColor 0UL == White)
  = getWosize_spec 0UL;
    FStar.UInt.shift_right_value_lemma #64 0 10;
    assert (getWosize 0UL == 0UL);
    getTag_spec 0UL;
    and0 255;
    assert (getTag 0UL == 0UL);
    getColor_raw 0UL;
    FStar.UInt.shift_right_value_lemma #64 0 8;
    assert_norm (pow2 8 == 256);
    FStar.Math.Lemmas.small_div 0 (pow2 8);
    assert (0 / pow2 8 == 0);
    assert (FStar.UInt.shift_right #64 0 8 == 0 / pow2 8);
    assert (FStar.UInt.shift_right #64 0 8 == 0);
    FStar.Classical.forall_intro and0;
    assert (get_color 0 == 0);
    assert (getColor 0UL == White)

/// ---------------------------------------------------------------------------
/// A and B
/// ---------------------------------------------------------------------------

let hA : U64.t = makeHeader 2UL White 0UL
let hB : U64.t = makeHeader 1UL White 0UL

let hA_facts () : Lemma (getWosize hA == 2UL /\ getTag hA == 0UL /\ getColor hA == White /\
                         getWosize hB == 1UL /\ getTag hB == 0UL /\ getColor hB == White)
  = makeHeader_getWosize 2UL White 0UL;
    makeHeader_getTag 2UL White 0UL;
    makeHeader_getColor 2UL White 0UL;
    makeHeader_getWosize 1UL White 0UL;
    makeHeader_getTag 1UL White 0UL;
    makeHeader_getColor 1UL White 0UL

let vA : obj_addr = U64.uint_to_t (za + 8)
let vB : U64.t = U64.uint_to_t (za + 32)

let g1 : heap = write_word z zero_addr hA
let g1b : heap =
  if za + 24 < heap_size then write_word g1 (U64.uint_to_t (za + 24)) hB else g1
let g2 : heap = write_word g1b vA vB

let obj_B (_: squash big) : obj_addr = vB
let hd_B (_: squash big) : hp_addr = U64.uint_to_t (za + 24)

#push-options "--z3rlimit 20"
let read_g2 (_: squash big) (a: hp_addr)
  : Lemma (read_word g2 a ==
           (if a = zero_addr then hA
            else if a = vA then vB
            else if U64.v a = za + 24 then hB
            else 0UL))
  = let p24 = hd_B () in
    read_write_same g1b vA vB;
    if a = vA then ()
    else begin
      read_write_different g1b vA a vB;
      read_write_same g1 p24 hB;
      if U64.v a = za + 24 then ()
      else begin
        read_write_different g1 p24 a hB;
        read_write_same z zero_addr hA;
        if a = zero_addr then ()
        else begin
          read_write_different z zero_addr a hA;
          read_zero a
        end
      end
    end
#pop-options

/// Members of `objects start g` lie after `start`.
#push-options "--z3rlimit 20 --fuel 2 --ifuel 1"
let rec objects_above (start: hp_addr) (g: heap) (x: obj_addr)
  : Lemma (requires Seq.mem x (objects start g))
          (ensures U64.v x >= U64.v start + 8)
          (decreases (Seq.length g - U64.v start))
  = Seq.mem_index x (objects start g);
    if U64.v start + 8 >= Seq.length g then
      assert (Seq.length (objects start g) == 0)
    else begin
      let wz = getWosize (read_word g start) in
      let next = U64.v start + (U64.v wz + 1) * 8 in
      if next > Seq.length g || next >= pow2 64 then
        assert (Seq.length (objects start g) == 0)
      else begin
        f_address_spec start;
        if next >= heap_size then begin
          assert (objects start g == Seq.cons (f_address start) Seq.empty);
          Seq.mem_cons (f_address start) (Seq.empty #obj_addr)
        end else begin
          let n : hp_addr = U64.uint_to_t next in
          assert (objects start g == Seq.cons (f_address start) (objects n g));
          Seq.mem_cons (f_address start) (objects n g);
          if x = f_address start then () else objects_above n g x
        end
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// The objects of g2
/// ---------------------------------------------------------------------------

let hd_A () : Lemma (hd_address vA == zero_addr) = hd_address_spec vA

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let objects_g2 (_: squash big)
  : Lemma (let b = obj_B () in
           Seq.mem vA (objects zero_addr g2) /\ Seq.mem b (objects zero_addr g2) /\
           hd_address b == hd_B () /\
           (forall (x: obj_addr). Seq.mem x (objects zero_addr g2) ==>
              x == vA \/ x == b \/ U64.v (hd_address x) >= za + 40))
  = let b = obj_B () in
    hd_address_spec b;
    hA_facts ();
    read_g2 () zero_addr;
    let p24 = hd_B () in
    let p40 : hp_addr = U64.uint_to_t (za + 40) in
    read_g2 () p24;
    f_address_spec zero_addr;
    f_address_spec p24;
    assert (objects zero_addr g2 == Seq.cons vA (objects p24 g2));
    assert (objects p24 g2 == Seq.cons b (objects p40 g2));
    Seq.mem_cons vA (objects p24 g2);
    Seq.mem_cons b (objects p40 g2);
    let rest (x: obj_addr)
      : Lemma (requires Seq.mem x (objects zero_addr g2))
              (ensures x == vA \/ x == b \/ U64.v (hd_address x) >= za + 40)
      = hd_address_spec x;
        if x = vA then ()
        else if x = b then ()
        else objects_above p40 g2 x
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires rest)
#pop-options

/// Every enumerated object's header: A's is hA, B's is hB, every other zero.
let header_g2 (_: squash big) (x: obj_addr)
  : Lemma (requires Seq.mem x (objects zero_addr g2))
          (ensures read_word g2 (hd_address x) ==
                   (if x = vA then hA else if x = obj_B () then hB else 0UL))
  = objects_g2 ();
    hd_address_spec x;
    read_g2 () (hd_address x)

let facts_g2 (_: squash big) (x: obj_addr)
  : Lemma (requires Seq.mem x (objects zero_addr g2))
          (ensures wosize_of_object x g2 ==
                     (if x = vA then 2UL else if x = obj_B () then 1UL else 0UL) /\
                   tag_of_object x g2 == 0UL /\
                   color_of_object x g2 == White /\
                   is_white x g2 /\ ~(is_gray x g2) /\ ~(is_black x g2) /\ ~(is_blue x g2) /\
                   ~(is_infix x g2) /\ ~(is_no_scan x g2))
  = header_g2 () x;
    hA_facts (); zero_header ();
    wosize_of_object_spec x g2;
    tag_of_object_spec x g2;
    color_of_object_spec x g2;
    is_white_iff x g2; is_gray_iff x g2; is_black_iff x g2; is_blue_iff x g2;
    is_infix_spec x g2; is_no_scan_spec x g2;
    infix_tag_val (); no_scan_tag_val ()

/// The fields of A and B.
let fields_g2 (_: squash big)
  : Lemma (let b = obj_B () in
           HeapGraph.get_field g2 vA 1UL == vB /\ HeapGraph.get_field g2 vA 2UL == 0UL /\
           HeapGraph.get_field g2 b 1UL == 0UL /\
           HeapGraph.is_pointer_field vB /\ ~(HeapGraph.is_pointer_field 0UL))
  = let b = obj_B () in
    hd_address_spec vA; hd_address_spec b;
    read_g2 () vA;
    read_g2 () (U64.uint_to_t (za + 16));
    read_g2 () (U64.uint_to_t (za + 32))

/// ---------------------------------------------------------------------------
/// g2 is well formed
/// ---------------------------------------------------------------------------

/// The only pointer field is A's first, which points to B.
#push-options "--z3rlimit 40 --fuel 3 --ifuel 1"
let efp_g2 (_: squash big) (x dst: obj_addr)
  : Lemma (requires Seq.mem x (objects zero_addr g2) /\
                    U64.v (wosize_of_object x g2) < pow2 54 /\
                    exists_field_pointing_to_unchecked g2 x (wosize_of_object x g2) dst)
          (ensures x == vA /\ dst == obj_B ())
  = facts_g2 () x;
    let b = obj_B () in
    hd_address_spec b;
    hd_address_spec dst;
    if x = vA then begin
      read_g2 () vA;
      read_g2 () (U64.uint_to_t (za + 16));
      assert (U64.add_mod vA (U64.mul_mod 1UL mword) == U64.uint_to_t (za + 16));
      assert (U64.add_mod vA (U64.mul_mod 0UL mword) == vA)
    end else if x = b then begin
      read_g2 () b;
      assert (U64.add_mod b (U64.mul_mod 0UL mword) == b)
    end
#pop-options

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let wf_g2 (_: squash big)
  : Lemma (well_formed_heap g2)
  = let b = obj_B () in
    objects_g2 ();
    facts_g2 () b;
    resolve_non_infix b g2;
    let p1 (x: obj_addr) : Lemma (requires Seq.mem x (objects zero_addr g2))
        (ensures U64.v (hd_address x) + 8 + (U64.v (wosize_of_object x g2) * 8) <= Seq.length g2) =
      facts_g2 () x; hd_address_spec x in
    FStar.Classical.forall_intro (FStar.Classical.move_requires p1);
    let p4 (x: obj_addr) : Lemma (requires Seq.mem x (objects zero_addr g2)) (ensures ~(is_infix x g2)) =
      facts_g2 () x in
    FStar.Classical.forall_intro (FStar.Classical.move_requires p4);
    let p2 (src dst: obj_addr)
      : Lemma (requires Seq.mem src (objects zero_addr g2) /\ fields_constrained g2 src /\
                        (let wz = wosize_of_object src g2 in
                         U64.v wz < pow2 54 /\ exists_field_pointing_to_unchecked g2 src wz dst))
              (ensures Seq.mem (resolve_object dst g2) (objects zero_addr g2))
      = efp_g2 () src dst
    in
    well_formed_heap_part2_intro g2 p2;
    let p3 (src dst: obj_addr)
      : Lemma (requires Seq.mem src (objects zero_addr g2) /\ fields_constrained g2 src /\
                        (let wz = wosize_of_object src g2 in
                         U64.v wz < pow2 54 /\ exists_field_pointing_to_unchecked g2 src wz dst))
              (ensures infix_addr_wf g2 (objects zero_addr g2) dst)
      = efp_g2 () src dst;
        infix_addr_wf_intro g2 (objects zero_addr g2) dst
    in
    well_formed_heap_part3_intro g2 p3;
    reveal_opaque (`%well_formed_heap) well_formed_heap
#pop-options

/// The precondition, met, for any roots among A and B.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let g2_pre_roots (_: squash big) (roots: list obj_addr)
  : Lemma (requires forall (r: obj_addr). L.memP r roots ==> r == vA \/ r == obj_B ())
          (ensures mark_pre g2 roots)
  = wf_g2 ();
    objects_g2 ();
    let b = obj_B () in
    facts_g2 () vA; facts_g2 () b;
    resolve_non_infix vA g2;
    resolve_non_infix b g2;
    let col (x: obj_addr) : Lemma (requires Seq.mem x (objects zero_addr g2))
        (ensures ~(is_gray x g2) /\ ~(is_black x g2)) = facts_g2 () x in
    FStar.Classical.forall_intro (FStar.Classical.move_requires col);
    let npb (src dst: obj_addr)
      : Lemma (requires Seq.mem src (objects zero_addr g2) /\ ~(is_blue src g2) /\
                        fields_constrained g2 src /\ points_to g2 src dst)
              (ensures ~(is_blue (resolve_object dst g2) g2))
      = wosize_of_object_bound src g2;
        efp_g2 () src dst
    in
    FStar.Classical.forall_intro_2 (fun src dst -> FStar.Classical.move_requires (npb src) dst);
    assert (Mark.no_pointer_to_blue g2);
    assert (Mark.noGreyObjects g2);
    assert (Mark.no_black_objects g2)
#pop-options

#push-options "--fuel 3 --ifuel 1"
let g2_pre (_: squash big) : Lemma (mark_pre g2 [vA])
  = g2_pre_roots () [vA]

let g2_pre2 (_: squash big) : Lemma (mark_pre g2 [vA; obj_B ()])
  = g2_pre_roots () [vA; obj_B ()]
#pop-options
