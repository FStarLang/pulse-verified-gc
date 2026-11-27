/// ---------------------------------------------------------------------------
/// GC.SPOT.MutatorRun - a concrete run of the mutator-equivalence model
/// ---------------------------------------------------------------------------
///
/// Non-vacuity of `GC.Gen.Run.Simulation.executes` and of `step`'s program
/// cases: a tiny program, run from `initial_state ()`, with a concrete run of
/// `step` that carries it out.
///
///   p1. `Alloc` an object (tag 0, one field, the int 0, as `1UL`);
///   p2. `Alloc` another;
///   p3. `Write` the int 1 (`3UL`) into field 0 of the second;
///   p4. `Read` it back.
///
/// The real run allocates both in the nursery (at offsets 8 and 24), stores
/// with a nursery write, and reads.  No collection runs.  The nursery
/// steps carry the nursery's frame and shape (`nursery_alloc_frame`,
/// `nursery_store_frame`, with `GenInv.minor_heap_shape`), which are shown
/// here for these concrete nurseries: every word is an object's header or
/// reads as no header (`words_ok`).  No hypothesis.
///
/// (A pointer stored into the nursery would need that the word not read as
/// a nursery header, the nursery's trusted shape, which the layout of its
/// word -- derived, `GC.Gen.Run.Simulation.Enabled.word_layout_holds` --
/// does not give: so the stored value here is an int.)
///
/// The major heap is untouched, and that nothing in it is allocated at the
/// start comes from the run invariant at the initial state
/// (`GC.Gen.Run.Simulation.Program.initial_nothing_allocated`, which uses
/// `GC.Gen.Run.Invariant.initial_run_invariant`).

module GC.SPOT.MutatorRun

open FStar.Seq
open FStar.List.Tot
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.MinorHeap
open GC.Gen.Run.Step
open GC.Gen.Run.History
open GC.Gen.Run.Invariant
open GC.Model.Represents
open GC.Gen.Run.Simulation

module U64 = FStar.UInt64
module GBase = GC.Gen.Base
module I = GC.Model.Ideal
module P = GC.Gen.Run.Simulation.Program
module SpecHeap = GC.Spec.Heap
module GenInv = GC.Gen.HeapInvariant

#set-options "--fuel 2 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Nursery words
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 15 --fuel 0 --ifuel 0"
let read_write_different
      (h: GBase.minor_heap)
      (a1: U64.t{U64.v a1 + 8 <= GBase.minor_heap_size /\ U64.v a1 % 8 == 0})
      (a2: U64.t{U64.v a2 + 8 <= GBase.minor_heap_size /\ U64.v a2 % 8 == 0})
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

#push-options "--z3rlimit 15 --fuel 0 --ifuel 0"
let read_write_same
      (h: GBase.minor_heap)
      (a: U64.t{U64.v a + 8 <= GBase.minor_heap_size /\ U64.v a % 8 == 0})
      (v: U64.t)
  : Lemma (ensures minor_read_word (minor_write_word h a v) a == v)
  = SpecHeap.combine_decompose_identity v
#pop-options

let room () : Lemma (32 <= GBase.minor_heap_size) =
  GBase.minor_heap_size_at_least_two_one_field_objects ()

/// ---------------------------------------------------------------------------
/// The states
/// ---------------------------------------------------------------------------

let one : U64.t = 1UL
let init1 : seq U64.t = Seq.create 1 one

let r0_ (_: unit) : GTot real_state = initial_state ()

let alloc_e : event = Alloc InNursery 0UL 1 init1

/// The state after a nursery allocation of one field holding `one`.
let after_alloc (r: real_state) : GTot real_state =
  let res = minor_alloc_spec r.memory.nursery 1 0 in
  { r with memory = { r.memory with nursery =
      { res.ms_out with data = write_nursery_fields res.ms_out.data res.obj_addr init1 0 } } }

let r1_ (_: unit) : GTot real_state = after_alloc (r0_ ())
let r2_ (_: unit) : GTot real_state = after_alloc (r1_ ())

/// The word written: the int 1.
let w : U64.t = 3UL

let write_e : event = Write (Nursery 24UL) 0 w

let r3_ (_: unit) : GTot real_state =
  let ms = (r2_ ()).memory.nursery in
  { (r2_ ()) with memory = { (r2_ ()).memory with nursery =
      { ms with data = minor_write_word_t ms.data (nursery_slot 24UL 0) w } } }

let read_e : event = Read (Nursery 24UL) 0

/// ---------------------------------------------------------------------------
/// The nursery after each step
/// ---------------------------------------------------------------------------

/// A nursery whose objects are exactly those of `objs`, each one field
/// holding... the facts the steps use.
let nursery_one (ms: minor_state) : prop =
  minor_wf ms /\ U64.v ms.bump == 16 /\
  (forall (o: U64.t). Seq.mem o (minor_objects ms) <==> o == 8UL) /\
  minor_wosize ms 8UL == 1 /\ minor_tag ms 8UL == 0

let nursery_two (ms: minor_state) : prop =
  minor_wf ms /\ U64.v ms.bump == 32 /\
  (forall (o: U64.t). Seq.mem o (minor_objects ms) <==> o == 8UL \/ o == 24UL) /\
  minor_wosize ms 8UL == 1 /\ minor_tag ms 8UL == 0 /\
  minor_wosize ms 24UL == 1 /\ minor_tag ms 24UL == 0

let nursery_fields_one (d: GBase.minor_heap) (o: U64.t) (a: U64.t)
  : Lemma (requires o == a /\ U64.v a + 8 <= GBase.minor_heap_size /\ U64.v a % 8 == 0)
          (ensures write_nursery_fields d o init1 0 == minor_write_word d a one)
  = assert (nursery_slot o 0 == a);
    assert (Seq.index init1 0 == one);
    let d' = minor_write_word_t d (nursery_slot o 0) one in
    assert (d' == minor_write_word d a one);
    assert (write_nursery_fields d o init1 0 == write_nursery_fields d' o init1 1);
    assert (write_nursery_fields d' o init1 1 == d')

let s2 : seq U64.t = Seq.cons 8UL (Seq.cons 24UL Seq.empty)

let mem_two (o: U64.t) : Lemma (Seq.mem o s2 <==> o == 8UL \/ o == 24UL) =
  Seq.mem_cons 8UL (Seq.cons 24UL (Seq.empty #U64.t));
  Seq.mem_cons 24UL (Seq.empty #U64.t)

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
/// The walk of a nursery with two one-field objects, at 8 and 24, laid out
/// to 32.
let walk_two_objs (ms: minor_state)
  : Lemma (requires U64.v ms.bump == 32 /\ minor_wosize ms 8UL == 1 /\ minor_tag ms 8UL == 0 /\
                    minor_wosize ms 24UL == 1 /\ minor_tag ms 24UL == 0)
          (ensures minor_wf ms /\ minor_objects ms == s2)
  = room ();
    let b = ms.bump in
    assert (U64.v b % 8 == 0);
    minor_objects_from_zero ms;
    minor_chain_walk_step ms.data 0 32 16;
    minor_chain_walk_step ms.data 16 32 32;
    minor_chain_walk_stop ms.data 32 32;
    assert (minor_objects ms `Seq.equal` s2)
#pop-options

let walk_two (ms: minor_state)
  : Lemma (requires U64.v ms.bump == 32 /\ minor_wosize ms 8UL == 1 /\ minor_tag ms 8UL == 0 /\
                    minor_wosize ms 24UL == 1 /\ minor_tag ms 24UL == 0)
          (ensures nursery_two ms)
  = walk_two_objs ms;
    FStar.Classical.forall_intro mem_two

#push-options "--z3rlimit 40"
let ms1_facts () : Lemma (nursery_one (r1_ ()).memory.nursery) =
  room ();
  let ms0 = (r0_ ()).memory.nursery in
  assert (U64.v ms0.bump == 0);
  let res = minor_alloc_spec ms0 1 0 in
  minor_alloc_success_layout ms0 1 0;
  minor_alloc_success_wosize ms0 1 0;
  minor_alloc_success_tag ms0 1 0;
  let d = res.ms_out.data in
  let d1 = minor_write_word d 8UL one in
  nursery_fields_one d res.obj_addr 8UL;
  assert (write_nursery_fields d res.obj_addr init1 0 == d1);
  read_write_different d 8UL 0UL one;
  let ms1 = (r1_ ()).memory.nursery in
  assert (ms1.data == d1);
  assert (minor_wosize ms1 8UL == 1);
  assert (minor_tag ms1 8UL == 0);
  minor_objects_from_zero ms1;
  minor_chain_walk_step d1 0 16 16;
  minor_chain_walk_stop d1 16 16;
  assert (minor_objects ms1 `Seq.equal` Seq.cons 8UL Seq.empty);
  Seq.mem_cons 8UL (Seq.empty #U64.t)
#pop-options

#push-options "--z3rlimit 40"
let ms2_facts () : Lemma (nursery_two (r2_ ()).memory.nursery) =
  room ();
  ms1_facts ();
  let ms1 = (r1_ ()).memory.nursery in
  let res = minor_alloc_spec ms1 1 0 in
  minor_alloc_success_layout ms1 1 0;
  minor_alloc_success_wosize ms1 1 0;
  minor_alloc_success_tag ms1 1 0;
  minor_alloc_preserves_word_outside_header ms1 1 0 0UL;
  let d = res.ms_out.data in
  let d2 = minor_write_word d 24UL one in
  nursery_fields_one d res.obj_addr 24UL;
  assert (write_nursery_fields d res.obj_addr init1 0 == d2);
  read_write_different d 24UL 0UL one;
  read_write_different d 24UL 16UL one;
  let ms2 = (r2_ ()).memory.nursery in
  assert (ms2.bump == res.ms_out.bump);
  assert (U64.v ms2.bump == 32);
  assert (ms2.data == d2);
  assert (minor_wosize ms2 8UL == 1);
  assert (minor_tag ms2 8UL == 0);
  assert (minor_wosize ms2 24UL == 1);
  assert (minor_tag ms2 24UL == 0);
  walk_two ms2
#pop-options

#push-options "--z3rlimit 40"
let ms3_data () : Lemma ((r3_ ()).memory.nursery.data ==
                          minor_write_word_t (r2_ ()).memory.nursery.data 24UL w /\
                          (r3_ ()).memory.nursery.bump == (r2_ ()).memory.nursery.bump) =
  room ();
  assert (nursery_slot 24UL 0 == 24UL)

let write_t_24 (h: GBase.minor_heap) (v: U64.t)
  : Lemma (requires 32 <= GBase.minor_heap_size)
          (ensures minor_write_word_t h 24UL v == minor_write_word h 24UL v)
  = ()

let ms3_facts () : Lemma (nursery_two (r3_ ()).memory.nursery) =
  room ();
  ms3_data ();
  write_t_24 (r2_ ()).memory.nursery.data w;
  ms2_facts ();
  let ms2 = (r2_ ()).memory.nursery in
  let d3 = minor_write_word ms2.data 24UL w in
  read_write_different ms2.data 24UL 0UL w;
  read_write_different ms2.data 24UL 16UL w;
  let ms3 = (r3_ ()).memory.nursery in
  assert (ms3.data == d3);
  assert (minor_wosize ms3 8UL == 1);
  assert (minor_wosize ms3 24UL == 1);
  assert (minor_tag ms3 8UL == 0);
  assert (minor_tag ms3 24UL == 0);
  assert (U64.v ms3.bump == 32);
  walk_two ms3
#pop-options

/// ---------------------------------------------------------------------------
/// The nursery's shape (`GenInv.minor_heap_shape`)
/// ---------------------------------------------------------------------------

/// A word that does not read as a header: wosize 0, not the infix tag.
let small_word (x: U64.t) : prop =
  U64.v (U64.shift_right x 10ul) == 0 /\ U64.v (U64.logand x 0xFFUL) <> 249

let small_consts () : Lemma (small_word 0UL /\ small_word 1UL /\ small_word 3UL) =
  assert_norm (small_word 0UL /\ small_word 1UL /\ small_word 3UL)

/// Every word of the nursery is an object's header (tag 0) or reads as no
/// header.
let words_ok (ms: minor_state) : prop =
  forall (q: U64.t). U64.v q + 8 <= GBase.minor_heap_size /\ U64.v q % 8 == 0 ==>
    (Seq.mem (U64.uint_to_t (U64.v q + 8)) (minor_objects ms) /\ minor_tag ms (U64.uint_to_t (U64.v q + 8)) == 0) \/
    small_word (minor_read_word ms.data q)

#push-options "--z3rlimit 40"
let shape_of_words (ms: minor_state)
  : Lemma (requires minor_wf ms /\ words_ok ms) (ensures GenInv.minor_heap_shape ms)
  = reveal_opaque (`%minor_guards_complete) (minor_guards_complete ms);
    reveal_opaque (`%minor_infix_wf) (minor_infix_wf ms);
    let at (addr: U64.t)
      : Lemma (U64.v addr >= 8 /\ U64.v addr < GBase.minor_heap_size /\ U64.v addr % 8 == 0 ==>
               ((minor_wosize ms addr > 0 ==> Seq.mem addr (minor_objects ms) /\ minor_tag ms addr == 0) /\
                minor_tag ms addr <> 249))
      = if U64.v addr >= 8 && U64.v addr < GBase.minor_heap_size && U64.v addr % 8 = 0 then begin
          let q : U64.t = U64.uint_to_t (U64.v addr - 8) in
          assert (U64.uint_to_t (U64.v q + 8) == addr)
        end in
    FStar.Classical.forall_intro at;
    GenInv.minor_heap_shape_intro ms
#pop-options

/// ---------------------------------------------------------------------------
/// The words of each nursery
/// ---------------------------------------------------------------------------

let data1 (_: unit) : GTot GBase.minor_heap = (r1_ ()).memory.nursery.data
let data2 (_: unit) : GTot GBase.minor_heap = (r2_ ()).memory.nursery.data
let data3 (_: unit) : GTot GBase.minor_heap = (r3_ ()).memory.nursery.data

#push-options "--z3rlimit 40"
let data1_word (q: U64.t)
  : Lemma (requires U64.v q + 8 <= GBase.minor_heap_size /\ U64.v q % 8 == 0 /\ U64.v q <> 0)
          (ensures minor_read_word (data1 ()) q == (if U64.v q = 8 then one else 0UL))
  = room ();
    ms1_facts ();
    let ms0 = (r0_ ()).memory.nursery in
    let res = minor_alloc_spec ms0 1 0 in
    minor_alloc_success_layout ms0 1 0;
    let d = res.ms_out.data in
    nursery_fields_one d res.obj_addr 8UL;
    assert (data1 () == minor_write_word d 8UL one);
    if U64.v q = 8 then begin
      assert (q == 8UL);
      read_write_same d 8UL one
    end else begin
      read_write_different d 8UL q one;
      minor_alloc_preserves_word_outside_header ms0 1 0 q;
      minor_read_word_zero_heap q
    end

let data2_word (q: U64.t)
  : Lemma (requires U64.v q + 8 <= GBase.minor_heap_size /\ U64.v q % 8 == 0 /\ U64.v q <> 0 /\ U64.v q <> 16)
          (ensures minor_read_word (data2 ()) q == (if U64.v q = 8 || U64.v q = 24 then one else 0UL))
  = room ();
    ms1_facts ();
    let ms1 = (r1_ ()).memory.nursery in
    let res = minor_alloc_spec ms1 1 0 in
    assert (U64.v ms1.bump == 16 /\ minor_wf ms1);
    minor_alloc_success_layout ms1 1 0;
    assert (U64.v res.obj_addr == 24);
    let d = res.ms_out.data in
    nursery_fields_one d res.obj_addr 24UL;
    assert (data2 () == minor_write_word d 24UL one);
    if U64.v q = 24 then begin
      assert (q == 24UL);
      read_write_same d 24UL one
    end else begin
      read_write_different d 24UL q one;
      minor_alloc_preserves_word_outside_header ms1 1 0 q;
      data1_word q
    end

let data3_word (q: U64.t)
  : Lemma (requires U64.v q + 8 <= GBase.minor_heap_size /\ U64.v q % 8 == 0)
          (ensures minor_read_word (data3 ()) q ==
                   (if U64.v q = 24 then w else minor_read_word (data2 ()) q))
  = room ();
    ms3_data ();
    write_t_24 (data2 ()) w;
    assert (data3 () == minor_write_word (data2 ()) 24UL w);
    if U64.v q = 24 then begin
      assert (q == 24UL);
      read_write_same (data2 ()) 24UL w
    end else
      read_write_different (data2 ()) 24UL q w
#pop-options

#push-options "--z3rlimit 40"
let ms1_shape () : Lemma (GenInv.minor_heap_shape (r1_ ()).memory.nursery) =
  ms1_facts ();
  small_consts ();
  let aux (q: U64.t) : Lemma (U64.v q + 8 <= GBase.minor_heap_size /\ U64.v q % 8 == 0 ==>
      (Seq.mem (U64.uint_to_t (U64.v q + 8)) (minor_objects (r1_ ()).memory.nursery) /\
       minor_tag (r1_ ()).memory.nursery (U64.uint_to_t (U64.v q + 8)) == 0) \/
      small_word (minor_read_word (r1_ ()).memory.nursery.data q)) =
    if U64.v q + 8 <= GBase.minor_heap_size && U64.v q % 8 = 0 then begin
      if U64.v q = 0 then assert (U64.uint_to_t (U64.v q + 8) == 8UL) else data1_word q
    end in
  FStar.Classical.forall_intro aux;
  shape_of_words (r1_ ()).memory.nursery

let ms2_shape () : Lemma (GenInv.minor_heap_shape (r2_ ()).memory.nursery) =
  ms2_facts ();
  small_consts ();
  let aux (q: U64.t) : Lemma (U64.v q + 8 <= GBase.minor_heap_size /\ U64.v q % 8 == 0 ==>
      (Seq.mem (U64.uint_to_t (U64.v q + 8)) (minor_objects (r2_ ()).memory.nursery) /\
       minor_tag (r2_ ()).memory.nursery (U64.uint_to_t (U64.v q + 8)) == 0) \/
      small_word (minor_read_word (r2_ ()).memory.nursery.data q)) =
    if U64.v q + 8 <= GBase.minor_heap_size && U64.v q % 8 = 0 then begin
      if U64.v q = 0 then assert (U64.uint_to_t (U64.v q + 8) == 8UL)
      else if U64.v q = 16 then assert (U64.uint_to_t (U64.v q + 8) == 24UL)
      else data2_word q
    end in
  FStar.Classical.forall_intro aux;
  shape_of_words (r2_ ()).memory.nursery

let ms3_shape () : Lemma (GenInv.minor_heap_shape (r3_ ()).memory.nursery) =
  ms3_facts ();
  small_consts ();
  let aux (q: U64.t) : Lemma (U64.v q + 8 <= GBase.minor_heap_size /\ U64.v q % 8 == 0 ==>
      (Seq.mem (U64.uint_to_t (U64.v q + 8)) (minor_objects (r3_ ()).memory.nursery) /\
       minor_tag (r3_ ()).memory.nursery (U64.uint_to_t (U64.v q + 8)) == 0) \/
      small_word (minor_read_word (r3_ ()).memory.nursery.data q)) =
    if U64.v q + 8 <= GBase.minor_heap_size && U64.v q % 8 = 0 then begin
      data3_word q;
      if U64.v q = 0 then assert (U64.uint_to_t (U64.v q + 8) == 8UL)
      else if U64.v q = 16 then assert (U64.uint_to_t (U64.v q + 8) == 24UL)
      else if U64.v q = 24 then ()
      else data2_word q
    end in
  FStar.Classical.forall_intro aux;
  shape_of_words (r3_ ()).memory.nursery
#pop-options

/// ---------------------------------------------------------------------------
/// Each step
/// ---------------------------------------------------------------------------

let field0 (ms: minor_state) (o: U64.t)
  : Lemma (requires U64.v o + 8 <= GBase.minor_heap_size /\ U64.v o % 8 == 0)
          (ensures minor_read_field ms o 0 == minor_read_word ms.data o)
  = assert (U64.uint_to_t (U64.v o + 0 * 8) == o)

/// The ints 0 and 1 (`1UL`, `3UL`) are no pointers, major or young.
let small_storable (r: real_state) (x: U64.t)
  : Lemma (requires r.phase == GC.Spec.Phase.Idle /\ (x == one \/ x == w))
          (ensures nursery_storable r x)
  = assert (~(is_pointer x));
    assert (GBase.to_minor_offset x == x)

let init1_facts () : Lemma (Seq.length init1 == 1 /\ Seq.index init1 0 == one) = ()
let lt1 (j: nat) : Lemma (requires j < 1) (ensures j == 0) = ()

/// The empty nursery has no objects.
let ms0_empty () : Lemma (forall (y: U64.t). ~(Seq.mem y (minor_objects (r0_ ()).memory.nursery))) =
  room ();
  minor_objects_from_zero (r0_ ()).memory.nursery;
  minor_chain_walk_stop (r0_ ()).memory.nursery.data 0 0

/// The new block's field: the word at 8 of the nursery after.
let field1 () : Lemma (minor_read_field (r1_ ()).memory.nursery 8UL 0 == one) =
  room ();
  data1_word 8UL;
  assert (data1 () == (r1_ ()).memory.nursery.data);
  field0 (r1_ ()).memory.nursery 8UL

/// The first allocation's frame, clause by clause (it was one query, which
/// was close to its budget and timed out in CI).
let frame1 () : Lemma (nursery_alloc_frame (r0_ ()).memory.nursery (r1_ ()).memory.nursery 8UL 0 init1) =
  ms1_facts ();
  ms1_shape ();
  ms0_empty ();
  field1 ();
  init1_facts ();
  let ms1 = (r1_ ()).memory.nursery in
  assert (minor_wosize ms1 8UL == Seq.length init1);
  introduce forall (j: nat). j < Seq.length init1 ==> minor_read_field ms1 8UL j == Seq.index init1 j
  with introduce _ ==> _ with lt1 j

let alloc1_addr () : Lemma ((minor_alloc_spec (r0_ ()).memory.nursery 1 0).obj_addr == 8UL) =
  room ();
  let ms0 = (r0_ ()).memory.nursery in
  minor_alloc_success_layout ms0 1 0;
  assert (U64.v (minor_alloc_spec ms0 1 0).obj_addr == 8)

/// The state after the first allocation is the one the step describes.
let r1_shape () : Lemma
  (let ms0 = (r0_ ()).memory.nursery in
   let res = minor_alloc_spec ms0 1 (U64.v 0UL) in
   r1_ () == { (r0_ ()) with memory = { (r0_ ()).memory with nursery =
                 { res.ms_out with data = write_nursery_fields res.ms_out.data res.obj_addr init1 0 } } })
  = assert_norm (U64.v 0UL == 0)

/// What the program owes: the initial word is storable, and can go in the
/// nursery; and there is room.
let alloc1_owed () : Lemma
  (init_storable (r0_ ()) 0UL init1 /\
   (I.tag_scannable 0UL ==> (forall (j: nat). j < Seq.length init1 ==> nursery_storable (r0_ ()) (Seq.index init1 j))) /\
   minor_can_alloc (r0_ ()).memory.nursery 1)
  = room ();
    init1_facts ();
    small_storable (r0_ ()) one;
    introduce forall (j: nat). j < Seq.length init1 ==> nursery_storable (r0_ ()) (Seq.index init1 j)
    with introduce _ ==> _ with lt1 j

let step1 () : Lemma (step (r0_ ()) alloc_e (r1_ ())) =
  room ();
  init1_facts ();
  frame1 ();
  alloc1_addr ();
  alloc1_owed ();
  r1_shape ();
  assert (nursery_alloc_step (r0_ ()) 0UL 1 init1 (r1_ ()))

let frame2 () : Lemma (nursery_alloc_frame (r1_ ()).memory.nursery (r2_ ()).memory.nursery 24UL 0 init1) =
  room ();
  ms1_facts ();
  ms2_facts ();
  ms2_shape ();
  data2_word 24UL;
  data2_word 8UL;
  data1_word 8UL;
  field0 (r2_ ()).memory.nursery 24UL;
  field0 (r2_ ()).memory.nursery 8UL;
  field0 (r1_ ()).memory.nursery 8UL;
  let ms1 = (r1_ ()).memory.nursery in
  let ms2 = (r2_ ()).memory.nursery in
  introduce forall (y: U64.t). Seq.mem y (minor_objects ms1) ==>
      y <> 24UL /\ minor_wosize ms2 y == minor_wosize ms1 y /\ minor_tag ms2 y == minor_tag ms1 y /\
      (forall (j: nat). j < minor_wosize ms1 y ==> minor_read_field ms2 y j == minor_read_field ms1 y j)
  with introduce _ ==> _ with begin
    assert (y == 8UL);
    introduce forall (j: nat). j < minor_wosize ms1 y ==> minor_read_field ms2 y j == minor_read_field ms1 y j
    with introduce _ ==> _ with lt1 j
  end;
  assert (GenInv.minor_heap_shape ms2);
  assert (forall (y: U64.t). Seq.mem y (minor_objects ms2) <==> Seq.mem y (minor_objects ms1) \/ y == 24UL);
  assert (minor_tag ms2 24UL == 0);
  init1_facts ();
  assert (minor_wosize ms2 24UL == Seq.length init1);
  introduce forall (j: nat). j < Seq.length init1 ==> minor_read_field ms2 24UL j == Seq.index init1 j
  with introduce _ ==> _ with lt1 j

let r2_shape () : Lemma
  (let ms1 = (r1_ ()).memory.nursery in
   let res = minor_alloc_spec ms1 1 (U64.v 0UL) in
   r2_ () == { (r1_ ()) with memory = { (r1_ ()).memory with nursery =
                 { res.ms_out with data = write_nursery_fields res.ms_out.data res.obj_addr init1 0 } } })
  = assert_norm (U64.v 0UL == 0)

let alloc2_owed () : Lemma
  (init_storable (r1_ ()) 0UL init1 /\
   (I.tag_scannable 0UL ==> (forall (j: nat). j < Seq.length init1 ==> nursery_storable (r1_ ()) (Seq.index init1 j))) /\
   minor_can_alloc (r1_ ()).memory.nursery 1)
  = room ();
    ms1_facts ();
    init1_facts ();
    small_storable (r1_ ()) one;
    introduce forall (j: nat). j < Seq.length init1 ==> nursery_storable (r1_ ()) (Seq.index init1 j)
    with introduce _ ==> _ with lt1 j

#push-options "--fuel 0 --ifuel 0"
let alloc2_addr () : Lemma ((minor_alloc_spec (r1_ ()).memory.nursery 1 0).obj_addr == 24UL) =
  room ();
  ms1_facts ();
  let ms1 = (r1_ ()).memory.nursery in
  assert (minor_wf ms1 /\ U64.v ms1.bump == 16);
  assert (minor_can_alloc ms1 1);
  minor_alloc_success_layout ms1 1 0;
  assert (U64.v (minor_alloc_spec ms1 1 0).obj_addr == 24)
#pop-options

let step2 () : Lemma (step (r1_ ()) alloc_e (r2_ ())) =
  room ();
  init1_facts ();
  frame2 ();
  alloc2_addr ();
  alloc2_owed ();
  r2_shape ();
  assert (nursery_alloc_step (r1_ ()) 0UL 1 init1 (r2_ ()))

let frame3 () : Lemma (nursery_store_frame (r2_ ()).memory.nursery (r3_ ()).memory.nursery 24UL 0 w) =
  room ();
  ms2_facts ();
  ms3_facts ();
  ms3_shape ();
  walk_two_objs (r2_ ()).memory.nursery;
  walk_two_objs (r3_ ()).memory.nursery;
  data3_word 24UL;
  data3_word 8UL;
  field0 (r3_ ()).memory.nursery 24UL;
  field0 (r3_ ()).memory.nursery 8UL;
  field0 (r2_ ()).memory.nursery 8UL;
  let ms2 = (r2_ ()).memory.nursery in
  let ms3 = (r3_ ()).memory.nursery in
  introduce forall (y: U64.t). Seq.mem y (minor_objects ms2) ==>
      minor_wosize ms3 y == minor_wosize ms2 y /\ minor_tag ms3 y == minor_tag ms2 y /\
      (forall (j: nat). j < minor_wosize ms2 y ==>
         minor_read_field ms3 y j == (if y = 24UL && j = 0 then w else minor_read_field ms2 y j))
  with introduce _ ==> _ with begin
    introduce forall (j: nat). j < minor_wosize ms2 y ==>
         minor_read_field ms3 y j == (if y = 24UL && j = 0 then w else minor_read_field ms2 y j)
    with introduce _ ==> _ with lt1 j
  end

let step3 (_: unit) : Lemma (step (r2_ ()) write_e (r3_ ())) =
  room ();
  ms2_facts ();
  frame3 ();
  small_storable (r2_ ()) w;
  ms3_data ()

let step4 () : Lemma (step (r3_ ()) read_e (r3_ ())) = ms3_facts ()

/// ---------------------------------------------------------------------------
/// The run
/// ---------------------------------------------------------------------------

let rn1_ (_: unit) : GTot (run (r0_ ()) ([] @ [alloc_e]) (r1_ ())) =
  step1 (); Step (Done (r0_ ())) alloc_e (r1_ ()) ()

let rn2_ (_: unit) : GTot (run (r0_ ()) (([] @ [alloc_e]) @ [alloc_e]) (r2_ ())) =
  step2 (); Step (rn1_ ()) alloc_e (r2_ ()) ()

let rn3 (_: unit) : GTot (run (r0_ ()) ((([] @ [alloc_e]) @ [alloc_e]) @ [write_e]) (r3_ ())) =
  step3 (); Step (rn2_ ()) write_e (r3_ ()) ()

let rn4 (_: unit) : GTot (run (r0_ ()) (((([] @ [alloc_e]) @ [alloc_e]) @ [write_e]) @ [read_e]) (r3_ ())) =
  step4 (); Step (rn3 ()) read_e (r3_ ()) ()

/// ---------------------------------------------------------------------------
/// The program
/// ---------------------------------------------------------------------------

let word1 : I.value = I.Word one

let p_alloc : I.program_event = I.Alloc 0UL 1 (I.Scannable (Seq.create 1 word1))
let p_write : I.program_event = I.Write 1 0 (I.Word w)
let p_read : I.program_event = I.Read 1 0

let ps1 = [p_alloc]
let ps2 = [p_alloc; p_alloc]
let ps3 = [p_alloc; p_alloc; p_write]
let ps4 = [p_alloc; p_alloc; p_write; p_read]

/// ---------------------------------------------------------------------------
/// The maps from blocks to objects
/// ---------------------------------------------------------------------------

let no_major (x: obj_addr) (r: real_state)
  : Lemma (requires r.memory.major == (r0_ ()).memory.major) (ensures ~(is_allocated r.memory (Major x)))
  = initial_run_invariant ();
    P.initial_nothing_allocated (Major x)

#push-options "--z3rlimit 40"
let ids1_facts (b: block_addr)
  : Lemma (ids_of_run (rn1_ ()) b == (if b = Nursery 8UL then Some 0 else None))
  = ms1_facts ();
    minor_objects_from_zero (r0_ ()).memory.nursery;
    minor_chain_walk_stop (r0_ ()).memory.nursery.data 0 0;
    match b with
    | Major x -> no_major x (r0_ ()); no_major x (r1_ ())
    | Nursery _ -> ()

let ids2_facts (b: block_addr)
  : Lemma (ids_of_run (rn2_ ()) b == (if b = Nursery 8UL then Some 0 else if b = Nursery 24UL then Some 1 else None))
  = ms1_facts ();
    ms2_facts ();
    ids1_facts b;
    assert (ids_of_run (rn2_ ()) b == update_block_ids (ids_of_run (rn1_ ())) 1 (r1_ ()) alloc_e (r2_ ()) b);
    match b with
    | Major x -> no_major x (r1_ ()); no_major x (r2_ ())
    | Nursery _ -> ()

let ids3_facts (_: unit) (b: block_addr)
  : Lemma (ids_of_run (rn3 ()) b == (if b = Nursery 8UL then Some 0 else if b = Nursery 24UL then Some 1 else None))
  = ms3_facts ();
    ids2_facts b;
    assert (ids_of_run (rn3 ()) b == update_block_ids (ids_of_run (rn2_ ())) 2 (r2_ ()) write_e (r3_ ()) b);
    match b with
    | Major x -> no_major x (r3_ ())
    | Nursery _ -> ()
#pop-options

/// ---------------------------------------------------------------------------
/// The run carries out the program
/// ---------------------------------------------------------------------------

let w_outside () : Lemma (outside_heaps w) =
  assert (GBase.to_minor_offset w == w)

let alloc_translates (m: real_memory) (ids: block_id_map) : Lemma (translates m ids alloc_e p_alloc) =
  assert (GBase.to_minor_offset one == one)

#push-options "--z3rlimit 40"
let write_translates (_: unit) : Lemma (translates (r2_ ()).memory (ids_of_run (rn2_ ())) write_e p_write) =
  ids2_facts (Nursery 24UL);
  ms2_facts ();
  assert (block_tag (r2_ ()).memory (Nursery 24UL) == 0);
  w_outside ()
#pop-options

let read_translates (_: unit) : Lemma (translates (r3_ ()).memory (ids_of_run (rn3 ())) read_e p_read) =
  ids3_facts () (Nursery 24UL)

#push-options "--z3rlimit 40"
let executes_1 () : Lemma (executes (rn1_ ()) ps1) =
  alloc_translates (r0_ ()).memory (ids_of_run (Done (r0_ ())));
  assert_norm (ps1 == [] @ [p_alloc])

let executes_2 () : Lemma (executes (rn2_ ()) ps2) =
  executes_1 ();
  alloc_translates (r1_ ()).memory (ids_of_run (rn1_ ()));
  assert_norm (ps2 == ps1 @ [p_alloc])

let executes_3 (_: unit) : Lemma (executes (rn3 ()) ps3) =
  executes_2 ();
  write_translates ();
  assert_norm (ps3 == ps2 @ [p_write])

let executes_4 (_: unit) : Lemma (executes (rn4 ()) ps4) =
  executes_3 ();
  read_translates ();
  assert_norm (ps4 == ps3 @ [p_read])
#pop-options

/// ---------------------------------------------------------------------------
/// The program is well formed
/// ---------------------------------------------------------------------------

let wf_alloc (m: I.ideal_memory) : Lemma (I.wf_event m p_alloc) =
  infix_tag_val ();
  no_scan_tag_val ();
  assert_norm (1 < pow2 54);
  assert (Seq.index (Seq.create 1 word1) 0 == word1)

#push-options "--z3rlimit 40 --fuel 5"
let wf_ps4 () : Lemma (I.wf_program ps4) =
  closure_tag_val ();
  wf_alloc I.empty_ideal;
  let m1 = I.ideal_step I.empty_ideal p_alloc in
  wf_alloc m1;
  let m2 = I.ideal_step m1 p_alloc in
  let m3 = I.ideal_step m2 p_write in
  assert (Seq.length m2.I.objects == 2);
  assert (Seq.index m2.I.roots 0 == I.Ptr { head = 0; infix_offset = 0 });
  assert (Seq.index m2.I.roots 1 == I.Ptr { head = 1; infix_offset = 0 });
  assert (I.root_names m2 0);
  assert (I.root_names m2 1);
  P.reachable_root m2 0;
  P.reachable_root m2 1;
  assert ((Seq.index m2.I.objects 1).I.tag == 0UL);
  assert (I.wf_event m2 p_write);
  assert (m3.I.roots == m2.I.roots);
  assert (Seq.length m3.I.objects == 2);
  assert (I.root_names m3 1);
  P.reachable_root m3 1;
  assert (I.wf_event m3 p_read)
#pop-options

/// ---------------------------------------------------------------------------
/// The result
/// ---------------------------------------------------------------------------

/// **A well-formed program and a legal run of `step` from the initial
/// state that carries it out**: `executes` and the program cases of `step`
/// -- nursery allocation, nursery write, read -- are satisfiable.
let mutator_run_exists (_: unit)
  : Lemma (exists (es: list event) (r: real_state) (rn: run (initial_state ()) es r).
             I.wf_program ps4 /\ executes rn ps4)
  = wf_ps4 ();
    executes_4 ()
