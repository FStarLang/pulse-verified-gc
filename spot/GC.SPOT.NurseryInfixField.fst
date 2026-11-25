module GC.SPOT.NurseryInfixField

/// SPOT audit: a **nursery object whose field is an interior pointer into a
/// major closure** is accepted by the collector's invariant, and survives a
/// minor collection.
///
/// This is what real OCaml does once a mutually recursive group
/// (`let rec f .. and g ..`) has been promoted: a record or a closure
/// environment allocated afterwards in the nursery is assigned `g`, which is an
/// interior pointer into the major closure.
///
/// The major heap is `GC.SPOT.InfixMajor`'s: a closure `P` whose body carries
/// an infix header, so `H` is an interior pointer into `P`.  The nursery holds
/// two blocks: a filler `F` of zeros at the bottom, and a one-field block `N`
/// (tag 0) at the very top, whose field is `H`.  `N` sits at the top because
/// `minor_guards_complete` reads every nursery word as a would-be header:
/// `H` is a major address, whose bits the abstract layout does not fix, and
/// the last word of the nursery is the only one that never heads a nursery
/// address.  The audit shows
///
///   * the pre-Phase-H.4 clause, stated on the raw field value, rejected it
///     (`H` is not an enumerated object) --- `spot_nf_raw_clause_rejects`;
///   * the resolved one accepts it, and so does the whole stop-the-world shape
///     `full_gc` demands --- `spot_nf_fields_no_blue`,
///     `spot_nf_collection_heap_shape`;
///   * the combined graph has the edge `N -> P` --- `spot_nf_edge_to_p`;
///   * after a minor collection with root `N` that promotes it, the copy's
///     field still holds `H`, `H` still names `P`, and the copy has an edge to
///     `P` in the heap graph --- `spot_nf_field_after_minor`.

module U64 = FStar.UInt64
module Seq = FStar.Seq

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Phase
open GC.Gen.Base
open GC.Gen.MinorHeap

module SpecHeap = GC.Spec.Heap
module SpecObj = GC.Spec.Object
module SpecFields = GC.Spec.Fields
module HeapGraph = GC.Spec.HeapGraph
module HeapModel = GC.Spec.HeapModel
module GenInv = GC.Gen.HeapInvariant
module Promote = GC.Gen.Promote
module Cheney = GC.Gen.Cheney
module CG = GC.Gen.CombinedGraph
module MinorFwd = GC.Gen.MinorCollectForwarding
module MCFH = GC.Gen.MinorCollectForwarding.Helpers
module MCFE = GC.Gen.MinorCollectForwarding.Edges
module MCFNE = GC.Gen.MinorCollectForwarding.NormalEdges
module CV = GC.Gen.CheneyGeneric
module InfixMajor = GC.SPOT.InfixMajor

/// ---------------------------------------------------------------------------
/// Sizes
/// ---------------------------------------------------------------------------

let room () : Lemma (32 <= minor_heap_size /\ minor_heap_size % 8 == 0 /\ minor_heap_size < pow2 57)
  = minor_heap_size_at_least_two_one_field_objects ()

/// The filler's size: everything below `N`'s two words and its own header.
let filler_wosize : nat = room (); minor_heap_size / 8 - 3

let filler_wosize_facts ()
  : Lemma (filler_wosize >= 1 /\ (filler_wosize + 1) * 8 == minor_heap_size - 16 /\
           filler_wosize * 1024 < pow2 64)
  = room (); assert_norm (pow2 64 == pow2 57 * 128)

/// The filler's header: wosize `filler_wosize`, colour 0, tag 0.
let filler_header : U64.t = filler_wosize_facts (); U64.uint_to_t (filler_wosize * 1024)

/// `N`'s header: wosize 1, colour 0, tag 0.
let n_header : U64.t = 1024UL

/// `N` and the two words below the top of the nursery.
let n_header_pos : U64.t = room (); U64.uint_to_t (minor_heap_size - 16)
let n_obj : U64.t = room (); U64.uint_to_t (minor_heap_size - 8)

let positions ()
  : Lemma (U64.v n_header_pos == minor_heap_size - 16 /\ U64.v n_obj == minor_heap_size - 8 /\
           U64.v n_header_pos % 8 == 0 /\ U64.v n_obj % 8 == 0 /\
           U64.v n_obj + 8 == minor_heap_size)
  = room ()

/// ---------------------------------------------------------------------------
/// The nursery
/// ---------------------------------------------------------------------------

let zero_nursery : minor_heap = Seq.create minor_heap_size 0uy

#push-options "--z3rlimit 15 --fuel 0 --ifuel 0"
let read_write_same
      (h: minor_heap)
      (a: U64.t{U64.v a + 8 <= minor_heap_size /\ U64.v a % 8 == 0})
      (v: U64.t)
  : Lemma (ensures minor_read_word (minor_write_word h a v) a == v)
  = SpecHeap.combine_decompose_identity v

let read_write_different
      (h: minor_heap)
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

let nursery_data (r: unit{InfixMajor.spot_infix_room}) : minor_heap =
  positions ();
  let d1 = minor_write_word zero_nursery 0UL filler_header in
  let d2 = minor_write_word d1 n_header_pos n_header in
  minor_write_word d2 n_obj (InfixMajor.spot_h r <: U64.t)

let nursery (r: unit{InfixMajor.spot_infix_room}) : minor_state =
  room ();
  { data = nursery_data r; bump = U64.uint_to_t minor_heap_size }

#push-options "--fuel 0 --ifuel 1"
let nursery_facts (r: unit{InfixMajor.spot_infix_room})
  : Lemma ((nursery r).data == nursery_data r /\ U64.v (nursery r).bump == minor_heap_size)
  = room ()
#pop-options

/// Every word of the nursery.
#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
let nursery_read (r: unit{InfixMajor.spot_infix_room})
    (a: U64.t{U64.v a + 8 <= minor_heap_size /\ U64.v a % 8 == 0})
  : Lemma (minor_read_word (nursery_data r) a ==
           (if U64.v a = 0 then filler_header
            else if U64.v a = minor_heap_size - 16 then n_header
            else if U64.v a = minor_heap_size - 8 then (InfixMajor.spot_h r <: U64.t)
            else 0UL))
  = room ();
    positions ();
    let d1 = minor_write_word zero_nursery 0UL filler_header in
    let d2 = minor_write_word d1 n_header_pos n_header in
    if U64.v a = minor_heap_size - 8 then begin
      assert (a == n_obj);
      read_write_same d2 n_obj (InfixMajor.spot_h r <: U64.t)
    end else begin
      read_write_different d2 n_obj a (InfixMajor.spot_h r <: U64.t);
      if U64.v a = minor_heap_size - 16 then begin
        assert (a == n_header_pos);
        read_write_same d1 n_header_pos n_header
      end else begin
        read_write_different d1 n_header_pos a n_header;
        if U64.v a = 0 then begin
          assert (a == 0UL);
          read_write_same zero_nursery 0UL filler_header
        end else begin
          read_write_different zero_nursery 0UL a filler_header;
          minor_read_word_zero_heap a
        end
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Header decoding
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let filler_header_decode ()
  : Lemma (U64.v (U64.shift_right filler_header 10ul) == filler_wosize /\
           U64.v (U64.logand filler_header 0xFFUL) == 0)
  = filler_wosize_facts ();
    let x = filler_wosize * 1024 in
    assert (U64.v filler_header == x);
    FStar.UInt.shift_right_value_lemma #64 x 10;
    assert_norm (pow2 10 == 1024);
    FStar.Math.Lemmas.cancel_mul_div filler_wosize 1024;
    FStar.UInt.logand_mask #64 x 8;
    assert_norm (pow2 8 - 1 == 255);
    assert_norm (pow2 8 == 256);
    FStar.Math.Lemmas.cancel_mul_mod (filler_wosize * 4) 256;
    assert (x == (filler_wosize * 4) * 256)

let small_headers_decode ()
  : Lemma (U64.v (U64.shift_right n_header 10ul) == 1 /\
           U64.v (U64.logand n_header 0xFFUL) == 0 /\
           U64.v (U64.shift_right 0UL 10ul) == 0 /\
           U64.v (U64.logand 0UL 0xFFUL) == 0)
  = assert_norm (U64.v (U64.shift_right n_header 10ul) == 1);
    assert_norm (U64.v (U64.logand n_header 0xFFUL) == 0);
    FStar.UInt.shift_right_value_lemma #64 0 10;
    FStar.Math.Lemmas.small_div 0 (pow2 10);
    FStar.UInt.logand_le #64 0 255
#pop-options

/// A zero word decodes to size 0, tag 0.  Stated of a variable: the same
/// facts of the literal `0UL` are reduced away before they reach SMT.
#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let zero_word_decode (x: U64.t)
  : Lemma (requires x == 0UL)
          (ensures U64.v (U64.shift_right x 10ul) == 0 /\ U64.v (U64.logand x 0xFFUL) == 0)
  = FStar.UInt.shift_right_value_lemma #64 (U64.v x) 10;
    FStar.Math.Lemmas.small_div (U64.v x) (pow2 10);
    FStar.UInt.logand_le #64 (U64.v x) 255
#pop-options

/// `minor_wosize`/`minor_tag` through the header word just below.
#push-options "--z3rlimit 10 --fuel 0 --ifuel 1"
private let header_fields_at (ms: minor_state) (obj: U64.t)
    (hdr: U64.t{U64.v hdr + 8 <= minor_heap_size /\ U64.v hdr % 8 == 0}) (h: U64.t)
  : Lemma (requires U64.v obj == U64.v hdr + 8 /\ U64.v obj < minor_heap_size /\
                    minor_read_word ms.data hdr == h)
          (ensures minor_wosize ms obj == U64.v (U64.shift_right h 10ul) /\
                   minor_tag ms obj == U64.v (U64.logand h 0xFFUL))
  = ()
#pop-options

/// The header word below a nursery address.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 1"
let header_word_below (r: unit{InfixMajor.spot_infix_room}) (addr: U64.t)
  : Lemma (requires U64.v addr >= 8 /\ U64.v addr < minor_heap_size /\ U64.v addr % 8 == 0)
          (ensures (let ha : U64.t = U64.uint_to_t (U64.v addr - 8) in
                    U64.v ha + 8 <= minor_heap_size /\ U64.v ha % 8 == 0 /\
                    minor_wosize (nursery r) addr == U64.v (U64.shift_right (minor_read_word (nursery_data r) ha) 10ul) /\
                    minor_tag (nursery r) addr == U64.v (U64.logand (minor_read_word (nursery_data r) ha) 0xFFUL)))
  = nursery_facts r;
    FStar.Math.Lemmas.lemma_mod_sub (U64.v addr) 8 1;
    let ha : U64.t = U64.uint_to_t (U64.v addr - 8) in
    assert (U64.v ha + 8 <= minor_heap_size /\ U64.v ha % 8 == 0);
    header_fields_at (nursery r) addr ha (minor_read_word (nursery_data r) ha)
#pop-options

/// That word, by cases.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let header_word_cases (r: unit{InfixMajor.spot_infix_room}) (addr: U64.t)
  : Lemma (requires U64.v addr >= 8 /\ U64.v addr < minor_heap_size /\ U64.v addr % 8 == 0)
          (ensures (let ha : U64.t = U64.uint_to_t (U64.v addr - 8) in
                    U64.v ha + 8 <= minor_heap_size /\ U64.v ha % 8 == 0 /\
                    minor_read_word (nursery_data r) ha ==
                      (if U64.v addr = 8 then filler_header
                       else if U64.v addr = minor_heap_size - 8 then n_header
                       else 0UL)))
  = room ();
    FStar.Math.Lemmas.lemma_mod_sub (U64.v addr) 8 1;
    let ha : U64.t = U64.uint_to_t (U64.v addr - 8) in
    assert (U64.v ha == U64.v addr - 8);
    nursery_read r ha
#pop-options

/// Size and tag of every nursery address: `F` at 8, `N` at the top, and size
/// 0, tag 0 everywhere else below the top.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let nursery_header (r: unit{InfixMajor.spot_infix_room}) (addr: U64.t)
  : Lemma (requires U64.v addr >= 8 /\ U64.v addr < minor_heap_size /\ U64.v addr % 8 == 0)
          (ensures minor_tag (nursery r) addr == 0 /\
                   minor_wosize (nursery r) addr ==
                     (if U64.v addr = 8 then filler_wosize
                      else if U64.v addr = minor_heap_size - 8 then 1
                      else 0))
  = header_word_below r addr;
    header_word_cases r addr;
    let ha : U64.t = U64.uint_to_t (U64.v addr - 8) in
    let hw = minor_read_word (nursery_data r) ha in
    if U64.v addr = 8 then begin
      assert (hw == filler_header);
      filler_header_decode ()
    end else if U64.v addr = minor_heap_size - 8 then begin
      assert (hw == n_header);
      small_headers_decode ()
    end else begin
      assert (hw == 0UL);
      zero_word_decode hw
    end
#pop-options

/// ---------------------------------------------------------------------------
/// The walk: `F`, then `N`
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
private let walk_step_wz (data: minor_heap)
      (pos: nat{pos % 8 == 0 /\ pos + 8 <= minor_heap_size})
      (bump: nat{bump <= minor_heap_size /\ bump % 8 == 0})
      (wz: Prims.pos)
      (next: nat{next % 8 == 0 /\ next <= bump})
  : Lemma
      (requires
        U64.v (U64.shift_right (minor_read_word data (U64.uint_to_t pos)) 10ul) == wz /\
        U64.v (U64.logand (minor_read_word data (U64.uint_to_t pos)) 0xFFUL) == 0 /\
        pos + 8 <= bump /\ next == pos + (wz + 1) * 8)
      (ensures
        minor_chain_valid data pos bump == minor_chain_valid data next bump /\
        minor_chain_no_infix data pos bump == minor_chain_no_infix data next bump /\
        minor_objects_from data pos bump ==
          Seq.cons (U64.uint_to_t (pos + 8)) (minor_objects_from data next bump))
  = minor_chain_walk_step data pos bump next
#pop-options

#push-options "--z3rlimit 40 --fuel 0 --ifuel 1"
let nursery_wf_and_objects (r: unit{InfixMajor.spot_infix_room})
  : Lemma (minor_wf (nursery r) /\
           minor_objects (nursery r) == Seq.cons 8UL (Seq.cons n_obj Seq.empty))
  = room ();
    positions ();
    nursery_facts r;
    filler_wosize_facts ();
    filler_header_decode ();
    small_headers_decode ();
    let data = nursery_data r in
    let m = minor_heap_size in
    nursery_read r 0UL;
    nursery_read r n_header_pos;
    assert (U64.uint_to_t 0 == 0UL);
    assert (U64.uint_to_t (m - 16) == n_header_pos);
    walk_step_wz data 0 m filler_wosize (m - 16);
    walk_step_wz data (m - 16) m 1 m;
    minor_chain_walk_stop data m m;
    minor_objects_from_zero (nursery r);
    assert (U64.uint_to_t (0 + 8) == 8UL);
    assert (U64.uint_to_t (m - 16 + 8) == n_obj)
#pop-options

#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
let nursery_object_cases (r: unit{InfixMajor.spot_infix_room}) (obj: U64.t)
  : Lemma (Seq.mem obj (minor_objects (nursery r)) <==> (obj == 8UL \/ obj == n_obj))
  = nursery_wf_and_objects r;
    Seq.mem_cons 8UL (Seq.cons n_obj Seq.empty);
    Seq.mem_cons n_obj (Seq.empty #U64.t)
#pop-options

/// ---------------------------------------------------------------------------
/// The nursery's shape
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 30 --fuel 0 --ifuel 1"
let nursery_guards_complete (r: unit{InfixMajor.spot_infix_room})
  : Lemma (minor_guards_complete (nursery r))
  = reveal_opaque (`%minor_guards_complete) (minor_guards_complete (nursery r));
    let aux (addr: U64.t)
      : Lemma (requires U64.v addr >= 8 /\ U64.v addr < minor_heap_size /\ U64.v addr % 8 == 0 /\
                        minor_wosize (nursery r) addr > 0 /\
                        U64.v addr + minor_wosize (nursery r) addr * 8 <= minor_heap_size /\
                        minor_tag (nursery r) addr <> 249)
              (ensures Seq.mem addr (minor_objects (nursery r)))
      = nursery_header r addr;
        positions ();
        nursery_object_cases r addr
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let nursery_infix_wf (r: unit{InfixMajor.spot_infix_room})
  : Lemma (minor_infix_wf (nursery r))
  = reveal_opaque (`%minor_infix_wf) (minor_infix_wf (nursery r));
    let aux (addr: U64.t)
      : Lemma (requires is_infix_in_minor (nursery r) addr) (ensures False)
      = nursery_header r addr
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

let spot_nf_minor_heap_shape (r: unit{InfixMajor.spot_infix_room})
  : Lemma (GenInv.minor_heap_shape (nursery r))
  = nursery_wf_and_objects r;
    nursery_guards_complete r;
    nursery_infix_wf r;
    GenInv.minor_heap_shape_intro (nursery r)

/// ---------------------------------------------------------------------------
/// The nursery's fields
/// ---------------------------------------------------------------------------

/// A field read is the word at its offset.
#push-options "--z3rlimit 10 --fuel 0 --ifuel 1"
let field_word (ms: minor_state) (obj: U64.t) (j: nat) (off: U64.t)
  : Lemma (requires U64.v off == U64.v obj + j * 8 /\ U64.v off + 8 <= minor_heap_size /\
                    U64.v off % 8 == 0)
          (ensures minor_read_field ms obj j == minor_read_word ms.data off)
  = ()
#pop-options

/// The filler's fields are zeros.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 1"
let filler_field (r: unit{InfixMajor.spot_infix_room}) (j: nat)
  : Lemma (requires j < filler_wosize)
          (ensures minor_read_field (nursery r) 8UL j == 0UL)
  = room ();
    filler_wosize_facts ();
    nursery_facts r;
    let n = 8 + j * 8 in
    assert (n + 8 <= minor_heap_size - 16);
    FStar.Math.Lemmas.lemma_mod_plus 8 j 8;
    let off : U64.t = U64.uint_to_t n in
    field_word (nursery r) 8UL j off;
    nursery_read r off
#pop-options

/// `N`'s only field is `H`.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 1"
let n_field (r: unit{InfixMajor.spot_infix_room})
  : Lemma (minor_read_field (nursery r) n_obj 0 == (InfixMajor.spot_h r <: U64.t))
  = room ();
    positions ();
    nursery_facts r;
    field_word (nursery r) n_obj 0 n_obj;
    nursery_read r n_obj
#pop-options

/// The filler's fields are zeros; `N`'s only field is `H`.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let nursery_field (r: unit{InfixMajor.spot_infix_room}) (obj: U64.t) (j: nat)
  : Lemma (requires Seq.mem obj (minor_objects (nursery r)) /\ j < minor_scan_wosize (nursery r) obj)
          (ensures (obj == n_obj /\ j == 0 /\
                    minor_read_field (nursery r) obj j == (InfixMajor.spot_h r <: U64.t)) \/
                   (obj == 8UL /\ minor_read_field (nursery r) obj j == 0UL))
  = room ();
    positions ();
    nursery_object_cases r obj;
    minor_scan_wosize_cases (nursery r) obj;
    if obj = n_obj then begin
      nursery_header r n_obj;
      assert (U64.v n_obj <> 8 /\ U64.v n_obj = minor_heap_size - 8);
      assert (minor_wosize (nursery r) n_obj == 1);
      assert (minor_tag (nursery r) n_obj == 0);
      assert (minor_scan_wosize (nursery r) n_obj == 1);
      assert (minor_scan_wosize (nursery r) obj == 1);
      assert (j < 1);
      assert (j == 0);
      n_field r
    end else begin
      assert (obj == 8UL);
      nursery_header r 8UL;
      filler_field r j
    end
#pop-options

/// `H` lies in the major heap, above the nursery range: a pointer field, not a
/// nursery pointer.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let h_is_major (r: unit{InfixMajor.spot_infix_room})
  : Lemma (let h = (InfixMajor.spot_h r <: U64.t) in
           SpecFields.is_pointer_field h /\ HeapGraph.is_pointer_field h /\ is_val_addr h /\
           ~(Promote.is_minor_pointer h) /\ to_minor_offset h == h /\ U64.v h >= minor_heap_size)
  = InfixMajor.spot_infix_layout_facts r;
    InfixMajor.spot_infix_h_is_interior r;
    zero_addr_above_minor ();
    is_val_addr_spec (InfixMajor.spot_h r <: U64.t);
    to_minor_offset_stable_above_minor (InfixMajor.spot_h r <: U64.t)
#pop-options

let zero_not_pointer () : Lemma (~(SpecFields.is_pointer_field 0UL))
  = ()

/// ---------------------------------------------------------------------------
/// The cross-generation clause
/// ---------------------------------------------------------------------------

/// The clause as it was before Phase H.4: a major pointer field of a nursery
/// object must itself be a non-blue enumerated object.
let raw_minor_major_fields_no_blue (minor: minor_state) (major: heap) : prop =
  forall (obj: U64.t) (j: nat).
    Seq.mem obj (minor_objects minor) /\
    j < minor_scan_wosize minor obj /\
    SpecFields.is_pointer_field (minor_read_field minor obj j) ==>
    Seq.mem ((minor_read_field minor obj j) <: obj_addr) (SpecFields.objects zero_addr major) /\
    ~(SpecObj.is_blue ((minor_read_field minor obj j) <: obj_addr) major)

/// **Negative half.**  The raw clause rejects `N`: its field `H` is no
/// enumerated object.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 1"
let spot_nf_raw_clause_rejects (r: unit{InfixMajor.spot_infix_room})
  : Lemma (~(raw_minor_major_fields_no_blue (nursery r) (InfixMajor.spot_infix_heap r)))
  = room ();
    positions ();
    nursery_object_cases r n_obj;
    nursery_header r n_obj;
    minor_scan_wosize_cases (nursery r) n_obj;
    nursery_field r n_obj 0;
    h_is_major r;
    InfixMajor.spot_infix_h_not_enumerated r
#pop-options

/// **Positive half.**  The resolved clause accepts it: `H` is a well-formed
/// interior pointer, and the closure `P` it names is a live object.
#push-options "--z3rlimit 30 --fuel 0 --ifuel 1"
let spot_nf_fields_not_free (r: unit{InfixMajor.spot_infix_room})
  : Lemma (GenInv.minor_major_fields_not_free SpecFields.free_stw (nursery r) (InfixMajor.spot_infix_heap r))
  = let g = InfixMajor.spot_infix_heap r in
    let h (obj: U64.t) (j: nat)
      : Lemma (requires Seq.mem obj (minor_objects (nursery r)) /\
                        j < minor_scan_wosize (nursery r) obj /\
                        SpecFields.is_pointer_field (minor_read_field (nursery r) obj j))
              (ensures SpecFields.in_use SpecFields.free_stw g
                         (SpecObj.resolve_object ((minor_read_field (nursery r) obj j) <: obj_addr) g) /\
                       SpecObj.infix_addr_wf g (SpecFields.objects zero_addr g)
                         ((minor_read_field (nursery r) obj j) <: obj_addr))
      = nursery_field r obj j;
        zero_not_pointer ();
        InfixMajor.spot_infix_h_resolves_to_p r;
        InfixMajor.spot_infix_h_addr_wf r;
        InfixMajor.spot_infix_mem r;
        InfixMajor.spot_infix_p_reads r
    in
    GenInv.minor_major_fields_not_free_intro SpecFields.free_stw (nursery r) g h
#pop-options

let spot_nf_fields_no_blue (r: unit{InfixMajor.spot_infix_room})
  : Lemma (GenInv.minor_major_fields_no_blue (nursery r) (InfixMajor.spot_infix_heap r))
  = spot_nf_fields_not_free r;
    GenInv.minor_major_fields_not_free_stw (nursery r) (InfixMajor.spot_infix_heap r)

/// The whole stop-the-world shape that `full_gc` and `minor_collect` demand.
let spot_nf_collection_heap_shape (r: unit{InfixMajor.spot_infix_room})
  : Lemma (GenInv.collection_heap_shape (nursery r) (InfixMajor.spot_infix_heap r)
             (InfixMajor.spot_infix_fp r))
  = InfixMajor.spot_infix_major_heap_shape r;
    spot_nf_minor_heap_shape r;
    spot_nf_fields_no_blue r;
    GenInv.collection_heap_shape_intro (nursery r) (InfixMajor.spot_infix_heap r)
      (InfixMajor.spot_infix_fp r)

/// ---------------------------------------------------------------------------
/// The combined graph
/// ---------------------------------------------------------------------------

/// `N`'s field classifies as the closure `P` (not `H`, which is no vertex),
/// so the combined graph has the edge `N -> P`.
#push-options "--z3rlimit 30 --fuel 0 --ifuel 1"
let spot_nf_edge_to_p (r: unit{InfixMajor.spot_infix_room})
  : Lemma (let g = InfixMajor.spot_infix_heap r in
           let h = (InfixMajor.spot_h r <: U64.t) in
           CG.classify_minor_field (nursery r) g h == Some (CG.MajorV (InfixMajor.spot_p r <: U64.t)) /\
           CG.mem_ce (CG.MinorV n_obj, CG.MajorV (InfixMajor.spot_p r <: U64.t))
             (CG.build_combined_graph (nursery r) g SpecFields.free_stw))
  = let g = InfixMajor.spot_infix_heap r in
    let h = (InfixMajor.spot_h r <: U64.t) in
    room ();
    positions ();
    h_is_major r;
    InfixMajor.spot_infix_h_resolves_to_p r;
    InfixMajor.spot_infix_mem r;
    resolve_minor_non_infix (nursery r) h;
    nursery_object_cases r h;
    CG.classify_minor_field_major (nursery r) g h;
    nursery_object_cases r n_obj;
    nursery_header r n_obj;
    minor_scan_wosize_cases (nursery r) n_obj;
    nursery_field r n_obj 0;
    CG.minor_field_edge_intro (nursery r) g SpecFields.free_stw n_obj 0
      (CG.MajorV (InfixMajor.spot_p r <: U64.t))
#pop-options

/// ---------------------------------------------------------------------------
/// After a minor collection
/// ---------------------------------------------------------------------------

/// The root set: `N` alone.
let spot_nf_roots : seq U64.t = Seq.create 1 n_obj

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let spot_nf_roots_mem (root: U64.t)
  : Lemma (Seq.mem root spot_nf_roots <==> root == n_obj)
  = FStar.Seq.Base.lemma_create_len 1 n_obj;
    FStar.Seq.Base.lemma_index_create 1 n_obj 0;
    FStar.Seq.Properties.seq_mem_k spot_nf_roots 0;
    if Seq.mem root spot_nf_roots then begin
      let k = FStar.Seq.Properties.index_mem root spot_nf_roots in
      assert (k == 0)
    end
#pop-options

/// `N` is a valid nursery root.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 1"
let spot_nf_roots_valid (r: unit{InfixMajor.spot_infix_room})
  : Lemma (MCFH.roots_valid_for_minor_collection (nursery r) (InfixMajor.spot_infix_heap r) spot_nf_roots)
  = room ();
    positions ();
    nursery_object_cases r n_obj;
    nursery_header r n_obj;
    resolve_minor_non_infix (nursery r) n_obj;
    FStar.Classical.forall_intro spot_nf_roots_mem
#pop-options

/// **`N` survives a minor collection with its field.**  When the collection
/// promotes `N` as an ordinary object (`normal_vertex_ready`: it is forwarded,
/// and its image is not interior -- the form in which the minor-collection
/// theorems speak of promoted objects), the promoted copy's field still holds
/// `H`, `H` still names `P` in the heap after the collection, and the heap
/// graph has the edge from the copy to `P`.
#push-options "--z3rlimit 40 --fuel 0 --ifuel 1"
let spot_nf_field_after_minor (r: unit{InfixMajor.spot_infix_room})
  : Lemma
    (requires
      MCFH.normal_vertex_ready Idle (nursery r) (InfixMajor.spot_infix_heap r)
        (InfixMajor.spot_infix_fp r) spot_nf_roots (CG.MinorV n_obj))
    (ensures (
      let ms = nursery r in
      let g = InfixMajor.spot_infix_heap r in
      let fp = InfixMajor.spot_infix_fp r in
      let prom = Cheney.cheney_promote Idle ms g fp spot_nf_roots in
      let res = Cheney.cheney_collect_spec ms g fp spot_nf_roots in
      let img = prom.Promote.fwd_map n_obj in
      let h = (InfixMajor.spot_h r <: U64.t) in
      U64.v img + 8 <= heap_size /\
      SpecHeap.read_word res.Promote.mc_major (U64.uint_to_t (U64.v img)) == h /\
      SpecObj.resolve_object (h <: obj_addr) res.Promote.mc_major == InfixMajor.spot_p r /\
      MCFH.mem_graph_edge_at (HeapModel.create_graph_with SpecFields.free_stw res.Promote.mc_major)
        img (InfixMajor.spot_p r <: U64.t)))
  = let ms = nursery r in
    let g = InfixMajor.spot_infix_heap r in
    let fp = InfixMajor.spot_infix_fp r in
    let roots = spot_nf_roots in
    let p = (InfixMajor.spot_p r <: U64.t) in
    let u = CG.MinorV n_obj in
    let w = CG.MajorV p in
    room ();
    positions ();
    // the stop-the-world context
    spot_nf_collection_heap_shape r;
    spot_nf_roots_valid r;
    MinorFwd.stop_the_world_context ms g fp roots;
    CV.cheney_collect_spec_with_stw ms g fp roots;
    // `N` is a root, and `N -> P` an edge, so both are reachable
    let cg = CG.build_combined_graph ms g SpecFields.free_stw in
    let croots = CG.classify_roots ms g roots in
    spot_nf_edge_to_p r;
    spot_nf_roots_mem n_obj;
    nursery_object_cases r n_obj;
    nursery_header r n_obj;
    resolve_minor_non_infix ms n_obj;
    CG.classify_roots_minor_mem ms g roots n_obj;
    CG.minor_vertex_char ms g SpecFields.free_stw n_obj;
    CG.combined_reachable_root cg croots u;
    CG.combined_reachable_step cg croots u w;
    assert (MCFH.normal_src_reachable Idle ms g fp SpecFields.free_stw roots u);
    assert (MCFH.normal_src_reachable Idle ms g fp SpecFields.free_stw roots w);
    MCFNE.normal_edge_forward_ready_intro Idle ms g fp SpecFields.free_stw roots u w;
    // the field, and the edge, after the collection
    InfixMajor.spot_infix_layout_facts r;
    is_val_addr_spec p;
    nursery_field r n_obj 0;
    MCFE.promoted_minor_major_field_preserved Idle ms g fp SpecFields.free_stw roots n_obj p 0;
    MCFE.promoted_minor_major_edge_forwarded Idle ms g fp SpecFields.free_stw roots n_obj p 0
#pop-options
