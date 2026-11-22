/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Promote.FollowWitness - what the promotion now accepts
/// ---------------------------------------------------------------------------
///
/// Design doc §12.  A major heap with one closure `C` (wosize 3, tag 247)
/// whose second field is an infix header of offset 2, so `C + 16` is an
/// infix pointer into it (a `let rec`'s second function); and a nursery
/// with one object `A` (wosize 2, tag 0) whose fields are
///
///   * that infix pointer `C + 16`, into an old closure, and
///   * the word 249 (the OCaml int 124), which looks like an infix header
///     of offset 0: the address `A + 16` past it reads as infix.
///
/// The promotion's conditions hold of them (`fields_follow`, `roots_follow`
/// with a root at `A`, `major_targets`); akhil's do not (`minor_infix_wf`
/// fails at `A + 16`, `minor_major_fields_not_free` at `C + 16`).  The
/// heap's size is the page witnesses' assumption (`n_pages > 0`).

module GC.Spec.Pages.Promote.FollowWitness

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Lib.Header
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap

module U64 = FStar.UInt64
module GenInv = GC.Gen.HeapInvariant
module NW = GC.Spec.Pages.NurseryWitness
module NW2 = GC.Spec.Pages.NurseryWitness2
module Fw = GC.Spec.Pages.Promote.Follow
module Co = GC.Spec.Pages.Promote.Collect
module Sh = GC.Spec.Pages.Shape
module Ly = GC.Spec.Pages.Layout

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Room
/// ---------------------------------------------------------------------------

/// The closure fits after `zero_addr`.
let big : prop = U64.v zero_addr + 32 <= heap_size

let big_of_pages (_: unit) : Lemma (requires Ly.n_pages > 0) (ensures big)
  = Ly.heap_room ();
    GC.Spec.Pages.Params.params_ok ();
    Ly.cls_bounds 0;
    assert (Ly.page_bytes >= 16);
    let n = heap_size - U64.v zero_addr - 16 in
    if n < Ly.page_bytes then FStar.Math.Lemmas.small_div n Ly.page_bytes

let za : nat = U64.v zero_addr

let za_facts (_: unit) : Lemma (za % 8 == 0 /\ za >= 2048 /\ za >= minor_heap_size /\ za + 8 < heap_size /\ heap_size < pow2 57)
  = zero_addr_above_2048 (); zero_addr_above_minor ()

/// ---------------------------------------------------------------------------
/// The major heap: one closure with an infix header
/// ---------------------------------------------------------------------------

/// wosize 3, white, tag 247 (closure).
let hdrC : U64.t = 3319UL
/// offset 2, tag 249 (infix).
let infixH : U64.t = 2297UL

let addr_at (k: nat{k < 4}) : U64.t =
  za_facts (); assert_norm (pow2 57 + 24 < pow2 64); U64.uint_to_t (za + 8 * k)

let g3 : heap =
  za_facts ();
  if za + 32 <= heap_size then begin
    let z = Seq.create heap_size 0uy in
    let a0 : hp_addr = addr_at 0 in
    let a1 : hp_addr = addr_at 1 in
    let a2 : hp_addr = addr_at 2 in
    let a3 : hp_addr = addr_at 3 in
    write_word (write_word (write_word (write_word z a0 hdrC) a1 1UL) a2 infixH) a3 1UL
  end
  else Seq.create heap_size 0uy

/// The closure, and the infix pointer into it.
let xC : U64.t = addr_at 1
let pW : U64.t = addr_at 3

let pW_v (_: unit) : Lemma (U64.v pW == za + 24 /\ U64.v pW >= minor_heap_size /\ U64.v pW % 8 == 0)
  = za_facts (); assert_norm (pow2 57 + 24 < pow2 64)

let addrs (_: unit)
  : Lemma (requires big)
          (ensures U64.v (addr_at 0) == za /\ U64.v xC == za + 8 /\ U64.v (addr_at 2) == za + 16 /\
                   U64.v pW == za + 24 /\ za + 24 < heap_size /\ (za + 8) % 8 == 0 /\ (za + 16) % 8 == 0 /\
                   (za + 24) % 8 == 0)
  = za_facts ()

#push-options "--z3rlimit 40"
let g3_words (_: unit)
  : Lemma (requires big)
          (ensures read_word g3 (addr_at 0) == hdrC /\ read_word g3 (addr_at 2) == infixH)
  = za_facts ();
    addrs ();
    let z = Seq.create heap_size 0uy in
    let a0 : hp_addr = addr_at 0 in
    let a1 : hp_addr = addr_at 1 in
    let a2 : hp_addr = addr_at 2 in
    let a3 : hp_addr = addr_at 3 in
    let h1 = write_word z a0 hdrC in
    let h2 = write_word h1 a1 1UL in
    let h3 = write_word h2 a2 infixH in
    assert (g3 == write_word h3 a3 1UL);
    read_write_different h3 a3 a2 1UL;
    read_write_same h2 a2 infixH;
    read_write_different h3 a3 a0 1UL;
    read_write_different h2 a2 a0 infixH;
    read_write_different h1 a1 a0 1UL;
    read_write_same z a0 hdrC
#pop-options

/// A header word's fields, by arithmetic.
let hbits (hdr: U64.t)
  : Lemma (U64.v (U64.logand hdr 0xFFUL) == U64.v hdr % 256 /\ U64.v (U64.shift_right hdr 10ul) == U64.v hdr / 1024 /\
           U64.v (getTag hdr) == U64.v hdr % 256 /\ U64.v (getWosize hdr) == U64.v hdr / 1024)
  = getTag_spec hdr;
    getWosize_spec hdr;
    FStar.UInt.logand_mask #64 (U64.v hdr) 8;
    assert_norm (pow2 8 - 1 == 255);
    assert_norm (pow2 10 == 1024)

/// A header word whose colour bits are 0 is white.
let col0 (hdr: U64.t)
  : Lemma (requires (U64.v hdr / 256) % 4 == 0) (ensures getColor hdr == White)
  = getColor_spec hdr;
    get_color_val (U64.v hdr);
    FStar.UInt.shift_right_value_lemma #64 (U64.v hdr) 8;
    assert_norm (pow2 8 == 256);
    FStar.UInt.logand_mask #64 (U64.v hdr / 256) 2;
    assert_norm (pow2 2 - 1 == 3)

let decode (_: unit)
  : Lemma (U64.v (getWosize hdrC) == 3 /\ U64.v (getTag hdrC) == 247 /\ getColor hdrC == White /\
           U64.v (getTag infixH) == 249 /\ U64.v (getWosize infixH) == 2 /\
           U64.v (U64.logand infixH 0xFFUL) == 249 /\ U64.v (U64.shift_right infixH 10ul) == 2)
  = hbits hdrC;
    hbits infixH;
    col0 hdrC

/// The walk starts with the closure; the rest lies past it.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
let walk_head (_: unit)
  : Lemma (requires big)
          (ensures (let x : obj_addr = xC in
                    Seq.mem x (objects zero_addr g3) /\
                    (forall (y: obj_addr). Seq.mem y (objects zero_addr g3) ==> y == x \/ U64.v y > za + 32)))
  = za_facts ();
    addrs ();
    g3_words ();
    decode ();
    let x : obj_addr = xC in
    f_address_spec zero_addr;
    assert (read_word g3 zero_addr == hdrC);
    if za + 32 >= heap_size then
      FStar.Seq.Properties.mem_cons x (Seq.empty #obj_addr)
    else begin
      let nx : hp_addr = U64.uint_to_t (za + 32) in
      assert (objects zero_addr g3 == Seq.cons x (objects nx g3));
      FStar.Seq.Properties.mem_cons x (objects nx g3);
      let rest (y: obj_addr) : Lemma (Seq.mem y (objects nx g3) ==> U64.v y > za + 32)
        = objects_addresses_gt_start nx g3 y in
      FStar.Classical.forall_intro rest;
      let all (y: obj_addr) : Lemma (Seq.mem y (objects zero_addr g3) ==> y == x \/ U64.v y > za + 32)
        = FStar.Seq.Properties.mem_cons x (objects nx g3) in
      FStar.Classical.forall_intro all
    end
#pop-options

/// The closure is in use, and the infix pointer resolves to it.
#push-options "--z3rlimit 40"
let closure_facts (_: unit)
  : Lemma (requires big)
          (ensures (let x : obj_addr = xC in
                    let p : obj_addr = pW in
                    in_use free_stw g3 x /\ resolve_object p g3 == x /\ is_infix p g3 /\
                    infix_addr_wf g3 (objects zero_addr g3) p /\ ~(in_use free_stw g3 p)))
  = za_facts ();
    addrs ();
    g3_words ();
    decode ();
    walk_head ();
    let x : obj_addr = xC in
    let p : obj_addr = pW in
    hd_address_spec x;
    wosize_of_object_spec x g3;
    tag_of_object_spec x g3;
    color_of_object_spec x g3;
    is_blue_iff x g3;
    assert (Sh.hdr g3 (U64.v x + (2 - 1) * 8) == infixH);
    Co.infix_target_core g3 x 2 3 p;
    free_stw_ok ();
    free_def_ok_elim free_stw
#pop-options

/// ---------------------------------------------------------------------------
/// The nursery: one object, an infix pointer and the word 249
/// ---------------------------------------------------------------------------

/// wosize 2, colour 0, tag 0.
let hdrA : U64.t = 2048UL
let w249 : U64.t = 249UL

let room (_: unit) : Lemma (32 <= minor_heap_size) = NW2.room ()

[@@"opaque_to_smt"]
let data3 : minor_heap =
  room ();
  let z = Seq.create minor_heap_size 0uy in
  let d1 = minor_write_word z 0UL hdrA in
  let d2 = minor_write_word d1 8UL pW in
  minor_write_word d2 16UL w249

let nur3 : minor_state = { data = data3; bump = 24UL }

let objA : U64.t = 8UL

/// The root: a pointer to A.
let roots3 : seq U64.t = Seq.create 1 objA

#push-options "--ifuel 1"
let state_facts (_: unit) : Lemma (nur3.data == data3 /\ U64.v nur3.bump == 24) = ()
#pop-options

#push-options "--z3rlimit 30"
let words (_: unit)
  : Lemma (minor_read_word data3 0UL == hdrA /\ minor_read_word data3 8UL == pW /\
           minor_read_word data3 16UL == w249)
  = room ();
    reveal_opaque (`%data3) data3;
    let z = Seq.create minor_heap_size 0uy in
    let d1 = minor_write_word z 0UL hdrA in
    let d2 = minor_write_word d1 8UL pW in
    NW2.read_write_same d2 16UL w249;
    NW2.read_write_different d2 16UL 8UL w249;
    NW2.read_write_same d1 8UL pW;
    NW2.read_write_different d2 16UL 0UL w249;
    NW2.read_write_different d1 8UL 0UL pW;
    NW2.read_write_same z 0UL hdrA
#pop-options

let ndecode (_: unit)
  : Lemma (U64.v (U64.shift_right hdrA 10ul) == 2 /\ U64.v (U64.logand hdrA 0xFFUL) == 0 /\
           U64.v (U64.shift_right w249 10ul) == 0 /\ U64.v (U64.logand w249 0xFFUL) == 249)
  = hbits hdrA;
    hbits w249

#push-options "--ifuel 1"
let header_at (obj: U64.t) (hdr: U64.t{U64.v hdr + 8 <= minor_heap_size /\ U64.v hdr % 8 == 0}) (h: U64.t)
  : Lemma (requires U64.v obj == U64.v hdr + 8 /\ U64.v obj < minor_heap_size /\ minor_read_word nur3.data hdr == h)
          (ensures minor_wosize nur3 obj == U64.v (U64.shift_right h 10ul) /\
                   minor_tag nur3 obj == U64.v (U64.logand h 0xFFUL))
  = ()
#pop-options

/// A: wosize 2, tag 0.  The address past the word 249 reads as infix, of
/// wosize 0.
let a_known (_: unit)
  : Lemma (minor_wosize nur3 objA == 2 /\ minor_tag nur3 objA == 0 /\
           minor_wosize nur3 24UL == 0 /\ minor_tag nur3 24UL == 249)
  = room (); state_facts (); words (); ndecode ();
    header_at objA 0UL hdrA;
    header_at 24UL 16UL w249

/// The walk: A alone.
#push-options "--z3rlimit 30"
let chain_facts (_: unit)
  : Lemma (minor_chain_valid data3 0 24 == true /\ minor_chain_no_infix data3 0 24 == true /\
           minor_objects_from data3 0 24 == Seq.cons objA Seq.empty)
  = room ();
    words ();
    ndecode ();
    assert (U64.uint_to_t 0 == 0UL);
    assert (minor_read_word data3 (U64.uint_to_t 0) == hdrA);
    NW2.walk_step_wz data3 0 24 2 24;
    minor_chain_walk_stop data3 24 24;
    assert (U64.uint_to_t (0 + 8) == objA)
#pop-options

let bump_facts (_: unit) : Lemma (U64.v nur3.bump <= minor_heap_size /\ U64.v nur3.bump % 8 == 0)
  = state_facts (); room (); assert_norm (24 % 8 == 0)

#push-options "--z3rlimit 30 --ifuel 1"
let wf_objects (_: unit)
  : Lemma (minor_wf nur3 /\ minor_objects nur3 == Seq.cons objA Seq.empty)
  = state_facts ();
    bump_facts ();
    chain_facts ();
    minor_objects_from_zero nur3
#pop-options

#push-options "--fuel 1"
let mem_objects (x: U64.t) : Lemma (Seq.mem x (minor_objects nur3) <==> x == objA)
  = wf_objects ();
    FStar.Seq.Properties.mem_cons objA (Seq.empty #U64.t)
#pop-options

/// A field read, at its word.
let rf (ms: minor_state) (obj: U64.t) (j: nat) (a: U64.t)
  : Lemma (requires U64.v obj + j * 8 + 8 <= minor_heap_size /\ (U64.v obj + j * 8) % 8 == 0 /\
                    U64.v a == U64.v obj + j * 8)
          (ensures minor_read_field ms obj j == minor_read_word ms.data a)
  = assert (U64.uint_to_t (U64.v obj + j * 8) == a)

/// A's fields: the infix pointer, then the word 249.
let objA_v (_: unit) : Lemma (U64.v objA == 8) = assert_norm (U64.v objA == 8)

/// The two fields of an object at 8 of any nursery holding these words.
#push-options "--ifuel 1"
let fields_gen (ms: minor_state) (d: minor_heap) (v0 v1: U64.t)
  : Lemma (requires ms.data == d /\ 32 <= minor_heap_size /\
                    minor_read_word d 8UL == v0 /\ minor_read_word d 16UL == v1)
          (ensures minor_read_field ms 8UL 0 == v0 /\ minor_read_field ms 8UL 1 == v1)
  = assert_norm (U64.v 8UL == 8 /\ U64.v 16UL == 16);
    rf ms 8UL 0 8UL;
    rf ms 8UL 1 16UL
#pop-options

let fields (_: unit)
  : Lemma (minor_read_field nur3 objA 0 == pW /\ minor_read_field nur3 objA 1 == w249)
  = state_facts (); words (); room ();
    assert_norm (objA == 8UL);
    fields_gen nur3 data3 pW w249

let small2 (j n: nat) : Lemma (requires j < n /\ n == 2) (ensures j == 0 \/ j == 1) = ()

let scan_j (obj: U64.t) (j: nat)
  : Lemma (requires Seq.mem obj (minor_objects nur3) /\ j < minor_scan_wosize nur3 obj)
          (ensures obj == objA /\ (j == 0 \/ j == 1))
  = mem_objects obj;
    a_known ();
    minor_scan_wosize_cases nur3 obj;
    assert (minor_scan_wosize nur3 obj == 2);
    small2 j (minor_scan_wosize nur3 obj)

/// ---------------------------------------------------------------------------
/// What the promotion asks holds
/// ---------------------------------------------------------------------------

/// Neither field is followed as an infix address: the pointer is a major
/// one, the word 249 is not aligned.
#push-options "--z3rlimit 30"
let field_follow (obj: U64.t) (j: nat)
  : Lemma (requires Seq.mem obj (minor_objects nur3) /\ j < minor_scan_wosize nur3 obj)
          (ensures Fw.follow_ok nur3 (to_minor_offset (minor_read_field nur3 obj j)))
  = scan_j obj j;
    fields ();
    za_facts ();
    if j = 0 then begin pW_v (); to_minor_offset_stable_above_minor pW end
    else assert_norm (U64.v w249 % 8 == 1)
#pop-options

let follows (_: unit) : Lemma (Fw.fields_follow nur3 /\ Fw.roots_follow nur3 roots3)
  = Fw.fields_follow_intro nur3 field_follow;
    a_known ();
    assert (Seq.index roots3 0 == objA)

/// The infix pointer's target is the closure, in use.
#push-options "--z3rlimit 30"
let target_one (obj: U64.t) (j: nat)
  : Lemma (requires big /\ Seq.mem obj (minor_objects nur3) /\ j < minor_scan_wosize nur3 obj /\
                    is_pointer_field (minor_read_field nur3 obj j))
          (ensures in_use free_stw g3 (resolve_object ((minor_read_field nur3 obj j) <: obj_addr) g3) /\
                   infix_addr_wf g3 (objects zero_addr g3) ((minor_read_field nur3 obj j) <: obj_addr))
  = scan_j obj j;
    fields ();
    if j = 1 then assert_norm (U64.v w249 % 8 == 1)
    else closure_facts ()
#pop-options

let targets (_: unit) : Lemma (requires big) (ensures Fw.major_targets free_stw nur3 g3)
  = Fw.major_targets_intro free_stw nur3 g3 target_one

/// ---------------------------------------------------------------------------
/// What akhil's conditions reject
/// ---------------------------------------------------------------------------

/// `A + 16` reads as infix with offset 0: not the infix header of a closure.
let not_infix_wf (_: unit) : Lemma (~(minor_infix_wf nur3))
  = room ();
    a_known ();
    reveal_opaque (`%minor_infix_wf) (minor_infix_wf nur3);
    assert (is_infix_in_minor nur3 24UL)

/// The infix pointer is not a block.
#push-options "--z3rlimit 30"
let not_fields_not_free (_: unit)
  : Lemma (requires big) (ensures ~(GenInv.minor_major_fields_not_free free_stw nur3 g3))
  = closure_facts ();
    fields ();
    a_known ();
    mem_objects objA;
    minor_scan_wosize_cases nur3 objA;
    za_facts ();
    addrs ();
    assert (is_pointer_field pW);
    if FStar.IndefiniteDescription.strong_excluded_middle (GenInv.minor_major_fields_not_free free_stw nur3 g3) then
      GenInv.minor_major_fields_not_free_elim free_stw nur3 g3 objA 0
#pop-options

/// ---------------------------------------------------------------------------
/// The witness
/// ---------------------------------------------------------------------------

/// **The promotion accepts a young field holding an infix pointer into an
/// old closure, and one holding an int that looks like an infix header**;
/// akhil's conditions reject both.
let accepted (_: unit)
  : Lemma (requires Ly.n_pages > 0)
          (ensures minor_wf nur3 /\ Fw.fields_follow nur3 /\ Fw.roots_follow nur3 roots3 /\
                   Fw.major_targets free_stw nur3 g3 /\
                   ~(minor_infix_wf nur3) /\ ~(GenInv.minor_major_fields_not_free free_stw nur3 g3) /\
                   minor_read_field nur3 objA 0 == pW /\ minor_read_field nur3 objA 1 == w249 /\
                   (let p : obj_addr = (big_of_pages (); za_facts (); addrs (); pW) in
                    is_infix p g3 /\ ~(in_use free_stw g3 p)))
  = big_of_pages ();
    wf_objects ();
    follows ();
    targets ();
    not_infix_wf ();
    not_fields_not_free ();
    fields ();
    closure_facts ()
