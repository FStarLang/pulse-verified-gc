/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.NurseryWitness - a nursery with one object
/// ---------------------------------------------------------------------------
///
/// Plan §27.6.  For the witness of a minor collection that promotes: the
/// empty nursery with one object allocated (wosize 1, tag 0), its field
/// the immediate 0, and one root pointing at it.  It has the shape a minor
/// collection asks (`nur_shape`), and points at no major block, so its
/// major pointers are in use for any definition of free (`nur_fields`).

module GC.Spec.Pages.NurseryWitness

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

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

/// The empty nursery, of zeros.
let ms0 : minor_state = minor_init (Seq.create minor_heap_size 0uy)

/// One object of one field, tag 0.
let nur : minor_state = (minor_alloc_spec ms0 1 0).ms_out

/// Its address.
let nobj : U64.t = 8UL

/// The root: a pointer to it.
let nroots : seq U64.t = Seq.create 1 nobj

/// **The object**: in the nursery, of wosize 1 and tag 0; every other word
/// of the nursery is 0.
let nur_facts (_: unit)
  : Lemma (minor_wf nur /\ Seq.mem nobj (minor_objects nur) /\
           minor_wosize nur nobj == 1 /\ minor_tag nur nobj == 0 /\
           (forall (a: U64.t{U64.v a + 8 <= minor_heap_size /\ U64.v a % 8 == 0}).
              U64.v a <> 0 ==> minor_read_word nur.data a == 0UL))
  = minor_alloc_success_layout ms0 1 0;
    minor_alloc_adds_object ms0 1 0;
    minor_alloc_success_wosize ms0 1 0;
    minor_alloc_success_tag ms0 1 0;
    let z (a: U64.t{U64.v a + 8 <= minor_heap_size /\ U64.v a % 8 == 0})
      : Lemma (U64.v a <> 0 ==> minor_read_word nur.data a == 0UL)
      = if U64.v a <> 0 then begin
          minor_alloc_preserves_word_outside_header ms0 1 0 a;
          minor_read_word_zero_heap a
        end
    in
    FStar.Classical.forall_intro z

/// Every field of a nursery object reads 0.
let nur_field (obj: U64.t) (j: nat)
  : Lemma (requires Seq.mem obj (minor_objects nur))
          (ensures minor_read_field nur obj j == 0UL)
  = nur_facts ();
    minor_objects_valid nur obj

/// A zero header: wosize 0, tag 0.
let zero_hdr (h: U64.t)
  : Lemma (requires h == 0UL)
          (ensures U64.v (U64.shift_right h 10ul) == 0 /\ U64.v (U64.logand h 0xFFUL) == 0)
  = assert (U64.v h == 0);
    assert (U64.v (U64.logand h 0xFFUL) == FStar.UInt.logand #64 0 255);
    FStar.UInt.logand_lemma_1 #64 255;
    FStar.UInt.logand_commutative #64 0 255;
    assert_norm (FStar.UInt.zero 64 == 0);
    assert (FStar.UInt.logand #64 0 255 == 0);
    FStar.UInt.shift_right_value_lemma #64 0 10

/// An address whose header word is 0 has wosize 0 and tag 0.
let zero_obj (addr: U64.t)
  : Lemma (requires U64.v addr >= 8 /\ U64.v addr < minor_heap_size /\ U64.v addr % 8 == 0 /\
                    minor_read_word nur.data (U64.uint_to_t (U64.v addr - 8)) == 0UL)
          (ensures minor_wosize nur addr == 0 /\ minor_tag nur addr == 0)
  = zero_hdr (minor_read_word nur.data (U64.uint_to_t (U64.v addr - 8)))

/// **It has the shape a minor collection asks.**
#push-options "--z3rlimit 30"
let nur_shape (_: unit) : Lemma (GenInv.minor_heap_shape nur)
  = nur_facts ();
    let hz (addr: U64.t)
      : Lemma (requires U64.v addr >= 8 /\ U64.v addr < minor_heap_size /\ U64.v addr % 8 == 0 /\ addr <> nobj)
              (ensures minor_wosize nur addr == 0 /\ minor_tag nur addr == 0)
      = assert (minor_read_word nur.data (U64.uint_to_t (U64.v addr - 8)) == 0UL);
        zero_obj addr
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires hz);
    reveal_opaque (`%minor_guards_complete) minor_guards_complete;
    reveal_opaque (`%minor_infix_wf) minor_infix_wf;
    assert (minor_guards_complete nur);
    assert (minor_infix_wf nur);
    GenInv.minor_heap_shape_intro nur
#pop-options

/// **It points at no major block.**
let nur_fields (free: free_def) (g: heap)
  : Lemma (GenInv.minor_major_fields_not_free free nur g)
  = let h (obj: U64.t) (j: nat)
      : Lemma (requires Seq.mem obj (minor_objects nur) /\ j < minor_scan_wosize nur obj /\
                        is_pointer_field (minor_read_field nur obj j))
              (ensures in_use free g (resolve_object ((minor_read_field nur obj j) <: obj_addr) g) /\
                       infix_addr_wf g (objects zero_addr g) ((minor_read_field nur obj j) <: obj_addr))
      = nur_field obj j
    in
    GenInv.minor_major_fields_not_free_intro free nur g h

/// The root is the object, a nursery address: no major pointer.
#push-options "--fuel 1"
let nroots_facts (_: unit)
  : Lemma ((forall (r: U64.t). Seq.mem r nroots ==> r == nobj) /\ ~(is_pointer nobj) /\
           Seq.length nroots == 1 /\ Seq.index nroots 0 == nobj)
  = zero_addr_above_2048 ();
    let one (r: U64.t) : Lemma (requires Seq.mem r nroots) (ensures r == nobj)
      = let i = FStar.Seq.Properties.index_mem r nroots in ()
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires one)
#pop-options
