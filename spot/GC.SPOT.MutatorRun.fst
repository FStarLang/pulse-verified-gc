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
///   p3. `Write` into field 0 of the second a pointer to the first;
///   p4. `Read` it back.
///
/// The real run allocates both in the nursery (at offsets 8 and 24), stores
/// the pointer with a nursery write, and reads it.  No collection runs.
///
/// One hypothesis: the trusted address layout of the stored pointer
/// (`GC.Model.Represents.word_layout`), which the spec cannot see because
/// `GC.Gen.Base.minor_base_addr` is abstract: the word of a pointer to the
/// nursery object at offset 8 is not a major-heap address and is the
/// nursery's base plus 8.  (With the bridge's layout -- the nursery below
/// `zero_addr` -- it holds.)
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

/// The word of a pointer to the first object.
let w : U64.t = ptr_value (Nursery 8UL) 0

let write_e : event = Write (Nursery 24UL) 0 w

let r3_ (_: unit) : GTot real_state =
  let ms = (r2_ ()).memory.nursery in
  { (r2_ ()) with memory = { (r2_ ()).memory with nursery =
      { ms with data = minor_write_word_t ms.data (nursery_slot 24UL 0) w } } }

let read_e : event = Read (Nursery 24UL) 0

/// The trusted layout of the stored word.
let layout_ok : prop = ~(is_pointer w) /\ U64.v (GBase.to_minor_offset w) == 8

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
/// Each step
/// ---------------------------------------------------------------------------

/// `1UL` (the int 0) is no pointer, major or young.
let one_storable (r: real_state) : Lemma (r.phase == GC.Spec.Phase.Idle ==> storable_value r one) =
  assert (~(is_pointer one));
  assert (GBase.to_minor_offset one == one)

let step1 () : Lemma (step (r0_ ()) alloc_e (r1_ ())) =
  room ();
  one_storable (r0_ ())

let step2 () : Lemma (step (r1_ ()) alloc_e (r2_ ())) =
  room ();
  ms1_facts ();
  one_storable (r1_ ())

#push-options "--z3rlimit 40"
let step3 (lay: squash layout_ok) : Lemma (step (r2_ ()) write_e (r3_ ())) =
  ms2_facts ();
  let ms = (r2_ ()).memory.nursery in
  let a = GBase.to_minor_offset w in
  assert (a == 8UL);
  assert (~(is_infix_in_minor ms a));
  assert (resolve_minor ms a == 8UL);
  assert (storable_value (r2_ ()) w)
#pop-options

let step4 () : Lemma (step (r3_ ()) read_e (r3_ ())) = ms3_facts ()

/// ---------------------------------------------------------------------------
/// The run
/// ---------------------------------------------------------------------------

let rn1_ (_: unit) : GTot (run (r0_ ()) ([] @ [alloc_e]) (r1_ ())) =
  step1 (); Step (Done (r0_ ())) alloc_e (r1_ ()) ()

let rn2_ (_: unit) : GTot (run (r0_ ()) (([] @ [alloc_e]) @ [alloc_e]) (r2_ ())) =
  step2 (); Step (rn1_ ()) alloc_e (r2_ ()) ()

let rn3 (lay: squash layout_ok) : GTot (run (r0_ ()) ((([] @ [alloc_e]) @ [alloc_e]) @ [write_e]) (r3_ ())) =
  step3 lay; Step (rn2_ ()) write_e (r3_ ()) ()

let rn4 (lay: squash layout_ok) : GTot (run (r0_ ()) (((([] @ [alloc_e]) @ [alloc_e]) @ [write_e]) @ [read_e]) (r3_ ())) =
  step4 (); Step (rn3 lay) read_e (r3_ ()) ()

/// ---------------------------------------------------------------------------
/// The program
/// ---------------------------------------------------------------------------

let word1 : I.value = I.Word one

let p_alloc : I.program_event = I.Alloc 0UL 1 (I.Scannable (Seq.create 1 word1))
let p_write : I.program_event = I.Write 1 0 (I.Ptr { head = 0; infix_offset = 0 })
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

let ids3_facts (lay: squash layout_ok) (b: block_addr)
  : Lemma (ids_of_run (rn3 lay) b == (if b = Nursery 8UL then Some 0 else if b = Nursery 24UL then Some 1 else None))
  = ms3_facts ();
    ids2_facts b;
    assert (ids_of_run (rn3 lay) b == update_block_ids (ids_of_run (rn2_ ())) 2 (r2_ ()) write_e (r3_ ()) b);
    match b with
    | Major x -> no_major x (r3_ ())
    | Nursery _ -> ()
#pop-options

/// ---------------------------------------------------------------------------
/// The run carries out the program
/// ---------------------------------------------------------------------------

let alloc_translates (ids: block_id_map) : Lemma (translates ids alloc_e p_alloc) =
  assert (GBase.to_minor_offset one == one)

#push-options "--z3rlimit 40"
let write_translates (lay: squash layout_ok) : Lemma (translates (ids_of_run (rn2_ ())) write_e p_write) =
  FStar.Classical.forall_intro ids2_facts;
  assert (ids_of_run (rn2_ ()) (Nursery 8UL) == Some 0)
#pop-options

let read_translates (lay: squash layout_ok) : Lemma (translates (ids_of_run (rn3 lay)) read_e p_read) =
  ids3_facts lay (Nursery 24UL)

#push-options "--z3rlimit 40"
let executes_1 () : Lemma (executes (rn1_ ()) ps1) =
  alloc_translates (ids_of_run (Done (r0_ ())));
  assert_norm (ps1 == [] @ [p_alloc])

let executes_2 () : Lemma (executes (rn2_ ()) ps2) =
  executes_1 ();
  alloc_translates (ids_of_run (rn1_ ()));
  assert_norm (ps2 == ps1 @ [p_alloc])

let executes_3 (lay: squash layout_ok) : Lemma (executes (rn3 lay) ps3) =
  executes_2 ();
  write_translates lay;
  assert_norm (ps3 == ps2 @ [p_write])

let executes_4 (lay: squash layout_ok) : Lemma (executes (rn4 lay) ps4) =
  executes_3 lay;
  read_translates lay;
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
  assert (I.valid_value m2 (I.Ptr { head = 0; infix_offset = 0 }));
  assert (I.usable m2 (I.Ptr { head = 0; infix_offset = 0 }));
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
/// state that carries it out** (given the trusted layout of the stored
/// pointer word): `executes` and the program cases of `step` -- nursery
/// allocation, nursery write, read -- are satisfiable.
let mutator_run_exists (lay: squash layout_ok)
  : Lemma (exists (es: list event) (r: real_state) (rn: run (initial_state ()) es r).
             I.wf_program ps4 /\ executes rn ps4)
  = wf_ps4 ();
    executes_4 lay
