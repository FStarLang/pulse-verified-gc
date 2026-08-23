/// ---------------------------------------------------------------------------
/// GC.Spec.SweepInv - Implementation
/// ---------------------------------------------------------------------------

module GC.Spec.SweepInv

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.HeapGraph

module U64 = FStar.UInt64

/// obj_in_objects: existential formulation to avoid U64.t/obj_addr coercion
let obj_in_objects (obj: U64.t) (g: heap) : prop =
  exists (a: obj_addr). U64.v a == U64.v obj /\ Seq.mem a (objects zero_addr g)

let fp_valid (fp: U64.t) (g: heap) : prop =
  is_pointer_field fp ==> obj_in_objects fp g

let obj_in_objects_intro (obj: obj_addr) (g: heap)
  = assert (U64.v obj == U64.v obj /\ Seq.mem obj (objects zero_addr g))

let fp_valid_not_pointer (fp: U64.t) (g: heap)
          = ()

let fp_valid_from_obj (fp: U64.t) (g: heap)
          = ()

let obj_in_objects_elim (obj: U64.t) (g: heap)
  = // From exists a: obj_addr. U64.v a == U64.v obj /\ mem a (objects zero_addr g)
    // a is obj_addr: U64.v a >= 8 /\ U64.v a < heap_size /\ U64.v a % 8 == 0
    // U64.v a == U64.v obj → obj satisfies obj_addr refinement
    // U64.v_inj gives a == obj, hence mem obj (objects zero_addr g)
    let _ = FStar.IndefiniteDescription.indefinite_description_ghost
      obj_addr (fun a -> U64.v a == U64.v obj /\ Seq.mem a (objects zero_addr g)) in
    ()

let fp_valid_elim (fp: U64.t) (g: heap)
  = if is_pointer_field fp then obj_in_objects_elim fp g

let fp_valid_transfer (fp: U64.t) (g1: heap) (g2: heap)
  = ()

let obj_in_objects_head (g: heap)
  = objects_nonempty_head zero_addr g;
    Seq.lemma_mem_snoc (Seq.empty #obj_addr) (f_address zero_addr);
    assert (Seq.mem (f_address zero_addr) (objects zero_addr g));
    obj_in_objects_intro (f_address zero_addr) g

/// ---------------------------------------------------------------------------
/// Heap density
/// ---------------------------------------------------------------------------

/// The walk from every position where objects > 0 continues at the next position
/// (provided the next position has room for a header), and the head of the next
/// position is in the global objects list.
/// Weakened density: only requires the chain property at positions whose
/// f_address is in objects zero_addr g (i.e., actual object header positions).
/// This excludes interior positions of large blocks that have 0UL headers
/// (phantom wosize-0 objects not in the global enumeration).
let heap_objects_dense (g: heap) : prop =
  forall (start: hp_addr).
    U64.v start + 8 < heap_size ==>
    Seq.mem (f_address start) (objects zero_addr g) ==>
    Seq.length (objects start g) > 0 ==>
    (let wz = getWosize (read_word g start) in
     let next = U64.v start + ((U64.v wz + 1) * 8) in
     next + 8 < heap_size ==>
     Seq.length (objects (U64.uint_to_t next) g) > 0 /\
     Seq.mem (f_address (U64.uint_to_t next)) (objects zero_addr g))

let heap_objects_dense_intro (g: heap)
  = ()

let objects_dense_step (start: hp_addr) (g: heap)
  = ()

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1"
let objects_dense_obj_in (start: hp_addr) (g: heap)
  = let wz = getWosize (read_word g start) in
    let next = U64.v start + ((U64.v wz + 1) * 8) in
    if next + 8 < heap_size then begin
      // From density: mem (f_address next_hp) (objects zero_addr g)
      let next_hp : hp_addr = U64.uint_to_t next in
      let oa = f_address next_hp in
      f_address_spec next_hp;
      assert (U64.v oa == next + 8);
      // density gives us Seq.mem oa (objects zero_addr g)
      obj_in_objects_intro oa g
    end
#pop-options

/// Transfer: density when objects lists and wosizes agree.
/// The key insight: objects is defined by getWosize(read_word), so equal wosizes
/// mean objects start g2 == objects start g1 for all start. Combined with
/// objects zero_addr equality (for global membership), density transfers directly.
#push-options "--z3rlimit 25 --fuel 2 --ifuel 1"
let rec objects_eq_from_wosize (start: hp_addr) (g1 g2: heap)
  : Lemma (requires Seq.length g1 == Seq.length g2 /\
                    (forall (p: hp_addr). getWosize (read_word g2 p) == getWosize (read_word g1 p)))
          (ensures objects start g2 == objects start g1)
          (decreases (Seq.length g1 - U64.v start))
  = if U64.v start + 8 >= Seq.length g1 then ()
    else begin
      let wz1 = getWosize (read_word g1 start) in
      let wz2 = getWosize (read_word g2 start) in
      assert (wz2 == wz1);
      let next = U64.v start + ((U64.v wz1 + 1) * 8) in
      if next > Seq.length g1 || next >= pow2 64 then ()
      else if next >= heap_size then ()
      else objects_eq_from_wosize (U64.uint_to_t next) g1 g2
    end
#pop-options

let heap_objects_dense_transfer (g1 g2: heap)
  = let aux (start: hp_addr) : Lemma
      (U64.v start + 8 < heap_size ==>
       Seq.mem (f_address start) (objects zero_addr g2) ==>
       Seq.length (objects start g2) > 0 ==>
       (let wz = getWosize (read_word g2 start) in
        let next = U64.v start + ((U64.v wz + 1) * 8) in
        next + 8 < heap_size ==>
        Seq.length (objects (U64.uint_to_t next) g2) > 0 /\
        Seq.mem (f_address (U64.uint_to_t next)) (objects zero_addr g2)))
    = if U64.v start + 8 < heap_size && Seq.mem (f_address start) (objects zero_addr g2) then begin
        // f_address start ∈ objects zero_addr g2 == objects zero_addr g1
        objects_eq_from_wosize start g1 g2;
        if Seq.length (objects start g2) > 0 then begin
          let wz = getWosize (read_word g2 start) in
          assert (wz == getWosize (read_word g1 start));
          let next = U64.v start + ((U64.v wz + 1) * 8) in
          if next + 8 < heap_size then begin
            objects_eq_from_wosize (U64.uint_to_t next) g1 g2
          end
        end
      end
    in
    FStar.Classical.forall_intro aux

/// Color change preserves density.
/// set_object_color writes colorHeader at hd_address obj. getWosize is invariant
/// under colorHeader, and read_word is unchanged at all other positions.
#push-options "--z3rlimit 15 --fuel 0 --ifuel 0"
let color_change_preserves_density (obj: obj_addr) (g: heap) (c: color)
  = let g' = set_object_color obj g c in
    // Prove: forall p. getWosize (read_word g' p) == getWosize (read_word g p)
    let wosize_eq (p: hp_addr) : Lemma
      (getWosize (read_word g' p) == getWosize (read_word g p))
    = if U64.v p = U64.v (hd_address obj) then
        colorHeader_preserves_wosize (read_word g (hd_address obj)) c
      else
        read_write_different g (hd_address obj) p (colorHeader (read_word g (hd_address obj)) c)
    in
    FStar.Classical.forall_intro wosize_eq;
    color_change_preserves_objects g obj c;
    heap_objects_dense_transfer g g'
#pop-options

/// Walk reconstruction: if f_address h ∈ objects zero_addr g and wfh g, then objects h g > 0
/// Proof: wfh gives object fits → objects h g is cons oa (...) → length > 0
#push-options "--z3rlimit 15 --fuel 2 --ifuel 1"
let member_implies_objects_nonempty (h: hp_addr{U64.v h + 8 < heap_size}) (g: heap)
  = let oa : obj_addr = f_address h in
    f_address_spec h;
    // oa = h + 8, oa ∈ objects zero_addr g
    // From well_formed_heap: hd_address oa + 8 + wz*8 <= Seq.length g
    GC.Spec.Heap.hd_address_spec oa;
    GC.Spec.Object.wosize_of_object_spec oa g;
    wf_object_size_bound g oa;
    // hd_address oa = h, so h + 8 + wz*8 <= heap_size
    // objects h g: check h + 8 >= heap_size? No: h + 8 = oa < heap_size ✓
    // wz = getWosize (read_word g h), next = h + (wz+1)*8 <= heap_size
    // next > heap_size fails, next >= pow2 64 fails (heap_size < pow2 64)
    // So objects h g = cons oa ... — length > 0
    ()
#pop-options

/// ---------------------------------------------------------------------------
/// Header preservation across sweep operations
/// ---------------------------------------------------------------------------

/// ---------------------------------------------------------------------------
/// Whiteness tracking implementation
/// ---------------------------------------------------------------------------

module SpecHeapForExit = GC.Spec.Heap

let no_gray_objects (g: heap) : prop =
  forall (obj: obj_addr). Seq.mem obj (objects zero_addr g) ==> ~(is_gray obj g)

module SpecHeap = GC.Spec.Heap

#push-options "--z3rlimit 25 --fuel 2 --ifuel 1"
let no_gray_elim (obj: obj_addr) (g: heap)
  = ()
#pop-options

let no_gray_intro (g: heap)
  = ()
