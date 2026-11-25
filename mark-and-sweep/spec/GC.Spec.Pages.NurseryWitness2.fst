/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.NurseryWitness2 - a nursery with two objects, one pointing
/// at the other
/// ---------------------------------------------------------------------------
///
/// Plan §27.6.  Two objects of one field each, tag 0: A at 8 (header at 0),
/// whose field holds a pointer to B; B at 24 (header at 16), whose field is
/// the immediate 0.  One root points at A.  A minor collection from it must
/// promote A, then, scanning A, promote B and rewrite A's copy to B's.
///
/// The nursery is built word by word, as akhil's
/// `spot/GC.SPOT.MinorInfixHeap` builds his; its word-level read/write
/// lemmas are copied from there (that module is not on the spec path).

module GC.Spec.Pages.NurseryWitness2

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap

module U64 = FStar.UInt64
module U8 = FStar.UInt8
module GenInv = GC.Gen.HeapInvariant
module NW = GC.Spec.Pages.NurseryWitness

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Words (akhil's, from `spot/GC.SPOT.MinorInfixHeap`)
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 15"
let read_write_same (h: minor_heap) (a: U64.t{U64.v a + 8 <= minor_heap_size /\ U64.v a % 8 == 0}) (v: U64.t)
  : Lemma (ensures minor_read_word (minor_write_word h a v) a == v)
  = GC.Spec.Heap.combine_decompose_identity v

let read_write_different (h: minor_heap)
      (a1: U64.t{U64.v a1 + 8 <= minor_heap_size /\ U64.v a1 % 8 == 0})
      (a2: U64.t{U64.v a2 + 8 <= minor_heap_size /\ U64.v a2 % 8 == 0})
      (v: U64.t)
  : Lemma (requires U64.v a1 <> U64.v a2)
          (ensures minor_read_word (minor_write_word h a1 v) a2 == minor_read_word h a2)
  = let a2v = U64.v a2 in
    let h' = minor_write_word h a1 v in
    assert (Seq.index h' (a2v + 0) == Seq.index h (a2v + 0));
    assert (Seq.index h' (a2v + 1) == Seq.index h (a2v + 1));
    assert (Seq.index h' (a2v + 2) == Seq.index h (a2v + 2));
    assert (Seq.index h' (a2v + 3) == Seq.index h (a2v + 3));
    assert (Seq.index h' (a2v + 4) == Seq.index h (a2v + 4));
    assert (Seq.index h' (a2v + 5) == Seq.index h (a2v + 5));
    assert (Seq.index h' (a2v + 6) == Seq.index h (a2v + 6));
    assert (Seq.index h' (a2v + 7) == Seq.index h (a2v + 7))
#pop-options

let room (_: unit) : Lemma (32 <= minor_heap_size) = minor_heap_size_at_least_two_one_field_objects ()

let room_fact : squash (32 <= minor_heap_size) = room ()

/// ---------------------------------------------------------------------------
/// The nursery
/// ---------------------------------------------------------------------------

/// wosize 1, colour 0, tag 0.
let hdr1 : U64.t = 1024UL

let data : minor_heap =
  let z = Seq.create minor_heap_size 0uy in
  let d1 = minor_write_word z 0UL hdr1 in
  let d2 = minor_write_word d1 8UL 24UL in
  minor_write_word d2 16UL hdr1

let nur2 : minor_state = { data = data; bump = 32UL }

let objA : U64.t = 8UL
let objB : U64.t = 24UL

let consts (_: unit) : Lemma (U64.v objA == 8 /\ U64.v objB == 24) = ()

/// The root: a pointer to A.
let roots2 : seq U64.t = Seq.create 1 objA

#push-options "--ifuel 1"
let state_facts (_: unit) : Lemma (nur2.data == data /\ U64.v nur2.bump == 32) = ()
#pop-options

/// Its words: A's header at 0, A's field at 8 (B), B's header at 16, the
/// rest 0.
#push-options "--z3rlimit 30"
let words (_: unit)
  : Lemma (minor_read_word data 0UL == hdr1 /\ minor_read_word data 8UL == 24UL /\
           minor_read_word data 16UL == hdr1 /\
           (forall (a: U64.t{U64.v a + 8 <= minor_heap_size /\ U64.v a % 8 == 0}).
              U64.v a <> 0 /\ U64.v a <> 8 /\ U64.v a <> 16 ==> minor_read_word data a == 0UL))
  = room ();
    let z = Seq.create minor_heap_size 0uy in
    let d1 = minor_write_word z 0UL hdr1 in
    let d2 = minor_write_word d1 8UL 24UL in
    read_write_same d2 16UL hdr1;
    read_write_different d2 16UL 8UL hdr1;
    read_write_same d1 8UL 24UL;
    read_write_different d2 16UL 0UL hdr1;
    read_write_different d1 8UL 0UL 24UL;
    read_write_same z 0UL hdr1;
    let o (a: U64.t{U64.v a + 8 <= minor_heap_size /\ U64.v a % 8 == 0})
      : Lemma (U64.v a <> 0 /\ U64.v a <> 8 /\ U64.v a <> 16 ==> minor_read_word data a == 0UL)
      = if U64.v a <> 0 && U64.v a <> 8 && U64.v a <> 16 then begin
          read_write_different d2 16UL a hdr1;
          read_write_different d1 8UL a 24UL;
          read_write_different z 0UL a hdr1;
          minor_read_word_zero_heap a
        end
    in
    FStar.Classical.forall_intro o
#pop-options

/// A word other than the three written is 0.
#push-options "--z3rlimit 30"
let word_zero (a: U64.t{U64.v a + 8 <= minor_heap_size /\ U64.v a % 8 == 0})
  : Lemma (requires U64.v a <> 0 /\ U64.v a <> 8 /\ U64.v a <> 16)
          (ensures minor_read_word data a == 0UL)
  = let z = Seq.create minor_heap_size 0uy in
    let d1 = minor_write_word z 0UL hdr1 in
    let d2 = minor_write_word d1 8UL 24UL in
    read_write_different d2 16UL a hdr1;
    read_write_different d1 8UL a 24UL;
    read_write_different z 0UL a hdr1;
    minor_read_word_zero_heap a
#pop-options

/// The header words decode.
let decode (_: unit)
  : Lemma (U64.v (U64.shift_right hdr1 10ul) == 1 /\ U64.v (U64.logand hdr1 0xFFUL) == 0 /\
           U64.v (U64.shift_right 24UL 10ul) == 0 /\ U64.v (U64.logand 24UL 0xFFUL) == 24)
  = assert_norm (U64.v (U64.shift_right hdr1 10ul) == 1);
    assert_norm (U64.v (U64.logand hdr1 0xFFUL) == 0);
    assert_norm (U64.v (U64.shift_right 24UL 10ul) == 0);
    assert_norm (U64.v (U64.logand 24UL 0xFFUL) == 24)

/// `minor_wosize`/`minor_tag` from the header word.
#push-options "--ifuel 1"
let header_fields_at (obj: U64.t) (hdr: U64.t{U64.v hdr + 8 <= minor_heap_size /\ U64.v hdr % 8 == 0}) (h: U64.t)
  : Lemma (requires U64.v obj == U64.v hdr + 8 /\ U64.v obj < minor_heap_size /\ minor_read_word nur2.data hdr == h)
          (ensures minor_wosize nur2 obj == U64.v (U64.shift_right h 10ul) /\
                   minor_tag nur2 obj == U64.v (U64.logand h 0xFFUL))
  = ()
#pop-options

/// **A and B**: wosize 1, tag 0; every other address has wosize 0, and tag
/// 0 or 24.
#push-options "--z3rlimit 30"
let objs_fields (addr: U64.t)
  : Lemma (requires U64.v addr >= 8 /\ U64.v addr < minor_heap_size /\ U64.v addr % 8 == 0)
          (ensures (if addr = objA || addr = objB then minor_wosize nur2 addr == 1 /\ minor_tag nur2 addr == 0
                    else minor_wosize nur2 addr == 0 /\ minor_tag nur2 addr <> 249))
  = state_facts ();
    room ();
    words ();
    decode ();
    let hn = U64.v addr - 8 in
    FStar.Math.Lemmas.lemma_mod_sub (U64.v addr) 8 1;
    let ha : U64.t = U64.uint_to_t hn in
    if hn = 0 then begin
      assert (ha == 0UL); header_fields_at addr 0UL hdr1
    end
    else if hn = 8 then begin
      assert (ha == 8UL); header_fields_at addr 8UL 24UL;
      assert (minor_wosize nur2 addr == 0 /\ minor_tag nur2 addr == 24)
    end
    else if hn = 16 then begin
      assert (ha == 16UL); header_fields_at addr 16UL hdr1
    end
    else begin
      assert (minor_read_word data ha == 0UL);
      header_fields_at addr ha 0UL;
      NW.zero_hdr 0UL
    end
#pop-options

/// One step of the walk across a header of known wosize (akhil's
/// `walk_step_wz`), in an empty context.
#push-options "--z3rlimit 10"
let walk_step_wz (d: minor_heap)
      (pos: nat{pos % 8 == 0 /\ pos + 8 <= minor_heap_size})
      (bump: nat{bump <= minor_heap_size /\ bump % 8 == 0})
      (wz: Prims.pos)
      (next: nat{next % 8 == 0 /\ next <= bump})
  : Lemma
      (requires U64.v (U64.shift_right (minor_read_word d (U64.uint_to_t pos)) 10ul) == wz /\
                pos + 8 <= bump /\ next == pos + (wz + 1) * 8)
      (ensures
        (let hdr = minor_read_word d (U64.uint_to_t pos) in
         let tag = U64.v (U64.logand hdr 0xFFUL) in
         minor_chain_valid d pos bump == minor_chain_valid d next bump /\
         minor_chain_no_infix d pos bump == (tag <> 249 && minor_chain_no_infix d next bump) /\
         minor_objects_from d pos bump == Seq.cons (U64.uint_to_t (pos + 8)) (minor_objects_from d next bump)))
  = minor_chain_walk_step d pos bump next

let bump_facts (_: unit)
  : Lemma (U64.v nur2.bump <= minor_heap_size /\ U64.v nur2.bump % 8 == 0)
  = state_facts (); room (); assert_norm (32 % 8 == 0)
#pop-options

let objA_known (_: unit) : Lemma (minor_wosize nur2 objA == 1 /\ minor_tag nur2 objA == 0)
  = room (); assert_norm (U64.v objA == 8); objs_fields objA

let objB_known (_: unit) : Lemma (minor_wosize nur2 objB == 1 /\ minor_tag nur2 objB == 0)
  = room (); assert_norm (U64.v objB == 24); assert_norm (24 % 8 == 0); objs_fields objB

/// A and B, in a clean context.
let objs_known (_: unit)
  : Lemma (minor_wosize nur2 objA == 1 /\ minor_tag nur2 objA == 0 /\
           minor_wosize nur2 objB == 1 /\ minor_tag nur2 objB == 0)
  = objA_known (); objB_known ()

/// The walk: A, then B.
#push-options "--z3rlimit 30 --fuel 1"
let wf_objects (_: unit)
  : Lemma (minor_wf nur2 /\ minor_objects nur2 == Seq.cons objA (Seq.cons objB Seq.empty))
  = state_facts ();
    room ();
    words ();
    decode ();
    assert (U64.uint_to_t 0 == 0UL);
    assert (U64.uint_to_t 16 == 16UL);
    walk_step_wz data 0 32 1 16;
    walk_step_wz data 16 32 1 32;
    minor_chain_walk_stop data 32 32;
    bump_facts ();
    minor_objects_from_zero nur2;
    assert (U64.uint_to_t (0 + 8) == objA);
    assert (U64.uint_to_t (16 + 8) == objB)
#pop-options

#push-options "--fuel 1"
let mem_objects (x: U64.t)
  : Lemma (Seq.mem x (minor_objects nur2) <==> x == objA \/ x == objB)
  = wf_objects ();
    FStar.Seq.Properties.mem_cons objA (Seq.cons objB Seq.empty);
    FStar.Seq.Properties.mem_cons objB (Seq.empty #U64.t)
#pop-options

/// The fields: A's points at B, B's is 0.
#push-options "--ifuel 1"
let fields (_: unit)
  : Lemma (minor_read_field nur2 objA 0 == objB /\ minor_read_field nur2 objB 0 == 0UL)
  = state_facts (); words (); room ();
    assert (U64.uint_to_t (U64.v objA + 0 * 8) == 8UL);
    assert (U64.uint_to_t (U64.v objB + 0 * 8) == 24UL);
    word_zero 24UL;
    let a8 : (a: U64.t{U64.v a + 8 <= minor_heap_size /\ U64.v a % 8 == 0}) = 8UL in
    assert (minor_read_word data a8 == 24UL)
#pop-options

/// **It has the shape a minor collection asks.**
#push-options "--z3rlimit 30"
let shape (_: unit) : Lemma (GenInv.minor_heap_shape nur2)
  = wf_objects ();
    FStar.Classical.forall_intro mem_objects;
    FStar.Classical.forall_intro (FStar.Classical.move_requires objs_fields);
    reveal_opaque (`%minor_guards_complete) minor_guards_complete;
    reveal_opaque (`%minor_infix_wf) minor_infix_wf;
    assert (minor_guards_complete nur2);
    assert (minor_infix_wf nur2);
    GenInv.minor_heap_shape_intro nur2
#pop-options

let small_j (j s: nat) : Lemma (requires j < s /\ s <= 1) (ensures j == 0) = ()

/// A field of A or B: B's address, or 0.
let scan_j (obj: U64.t) (j: nat)
  : Lemma (requires Seq.mem obj (minor_objects nur2) /\ j < minor_scan_wosize nur2 obj)
          (ensures j == 0 /\ (obj == objA \/ obj == objB))
  = mem_objects obj;
    minor_scan_wosize_cases nur2 obj;
    if obj = objA then begin
      objA_known ();
      small_j j (minor_scan_wosize nur2 obj)
    end else begin
      assert (obj == objB);
      objB_known ();
      small_j j (minor_scan_wosize nur2 obj)
    end

let field_val (obj: U64.t) (j: nat)
  : Lemma (requires Seq.mem obj (minor_objects nur2) /\ j < minor_scan_wosize nur2 obj)
          (ensures minor_read_field nur2 obj j == objB \/ minor_read_field nur2 obj j == 0UL)
  = scan_j obj j;
    fields ()

/// **It points at no major block**: its fields are nursery values.
#push-options "--z3rlimit 30"
let no_major (free: free_def) (g: heap)
  : Lemma (GenInv.minor_major_fields_not_free free nur2 g)
  = zero_addr_above_2048 ();
    fields ();
    let h (obj: U64.t) (j: nat)
      : Lemma (requires Seq.mem obj (minor_objects nur2) /\ j < minor_scan_wosize nur2 obj /\
                        is_pointer_field (minor_read_field nur2 obj j))
              (ensures in_use free g (resolve_object ((minor_read_field nur2 obj j) <: obj_addr) g) /\
                       infix_addr_wf g (objects zero_addr g) ((minor_read_field nur2 obj j) <: obj_addr))
      = field_val obj j;
        assert_norm (U64.v objB == 24)
    in
    GenInv.minor_major_fields_not_free_intro free nur2 g h
#pop-options

/// The root.
#push-options "--fuel 1"
let roots_facts (_: unit)
  : Lemma ((forall (r: U64.t). Seq.mem r roots2 ==> r == objA) /\ ~(is_pointer objA) /\
           Seq.length roots2 == 1 /\ Seq.index roots2 0 == objA)
  = zero_addr_above_2048 ();
    let one (r: U64.t) : Lemma (requires Seq.mem r roots2) (ensures r == objA)
      = let _ = FStar.Seq.Properties.index_mem r roots2 in ()
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires one)
#pop-options

/// B's address, read as a nursery pointer, is B.
let objB_offset (_: unit) : Lemma (to_minor_offset objB == objB)
  = room (); assert_norm (U64.v objB == 24); to_minor_offset_in_minor_range objB

/// A and B are nursery pointers.
let minor_ptrs (_: unit) : Lemma (GC.Gen.Promote.is_minor_pointer objA /\ GC.Gen.Promote.is_minor_pointer objB)
  = room (); assert_norm (U64.v objA == 8 /\ U64.v objB == 24)
