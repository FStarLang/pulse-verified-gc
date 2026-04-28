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
  exists (a: obj_addr). U64.v a == U64.v obj /\ Seq.mem a (objects 0UL g)

let fp_valid (fp: U64.t) (g: heap) : prop =
  is_pointer_field fp ==> obj_in_objects fp g

let sweep_post (g_pre g_post: heap) (new_fp: U64.t) : prop =
  well_formed_heap g_post /\
  objects 0UL g_post == objects 0UL g_pre /\
  fp_valid new_fp g_post

let obj_in_objects_intro (obj: obj_addr) (g: heap)
  : Lemma (requires Seq.mem obj (objects 0UL g))
          (ensures obj_in_objects obj g)
  = assert (U64.v obj == U64.v obj /\ Seq.mem obj (objects 0UL g))

let fp_valid_intro (fp: obj_addr) (g: heap)
  : Lemma (requires Seq.mem fp (objects 0UL g))
          (ensures fp_valid fp g)
  = obj_in_objects_intro fp g

let fp_valid_not_pointer (fp: U64.t) (g: heap)
  : Lemma (requires not (is_pointer_field fp))
          (ensures fp_valid fp g) = ()

let fp_valid_from_obj (fp: U64.t) (g: heap)
  : Lemma (requires obj_in_objects fp g)
          (ensures fp_valid fp g) = ()

let obj_in_objects_elim (obj: U64.t) (g: heap)
  : Lemma (requires obj_in_objects obj g)
          (ensures U64.v obj >= U64.v mword /\ U64.v obj < heap_size /\
                   U64.v obj % U64.v mword == 0 /\
                   Seq.mem (obj <: obj_addr) (objects 0UL g))
  = // From exists a: obj_addr. U64.v a == U64.v obj /\ mem a (objects 0UL g)
    // a is obj_addr: U64.v a >= 8 /\ U64.v a < heap_size /\ U64.v a % 8 == 0
    // U64.v a == U64.v obj → obj satisfies obj_addr refinement
    // U64.v_inj gives a == obj, hence mem obj (objects 0UL g)
    let _ = FStar.IndefiniteDescription.indefinite_description_ghost
      obj_addr (fun a -> U64.v a == U64.v obj /\ Seq.mem a (objects 0UL g)) in
    ()

let fp_valid_elim (fp: U64.t) (g: heap)
  : Lemma (requires fp_valid fp g)
          (ensures is_pointer_field fp ==>
                    (U64.v fp >= U64.v mword /\ U64.v fp < heap_size /\
                     U64.v fp % U64.v mword == 0 /\
                     Seq.mem (fp <: obj_addr) (objects 0UL g)))
  = if is_pointer_field fp then obj_in_objects_elim fp g

let sweep_post_intro (g_pre: heap) (g_post: heap) (new_fp: U64.t)
  : Lemma (requires well_formed_heap g_post /\
                    objects 0UL g_post == objects 0UL g_pre /\
                    fp_valid new_fp g_post)
          (ensures sweep_post g_pre g_post new_fp)
  = ()

let sweep_post_elim_wfh (g_pre: heap) (g_post: heap) (new_fp: U64.t)
  : Lemma (requires sweep_post g_pre g_post new_fp)
          (ensures well_formed_heap g_post) = ()

let sweep_post_elim_objects (g_pre: heap) (g_post: heap) (new_fp: U64.t)
  : Lemma (requires sweep_post g_pre g_post new_fp)
          (ensures objects 0UL g_post == objects 0UL g_pre) = ()

let sweep_post_elim_fp (g_pre: heap) (g_post: heap) (new_fp: U64.t)
  : Lemma (requires sweep_post g_pre g_post new_fp)
          (ensures fp_valid new_fp g_post) = ()

let fp_valid_transfer (fp: U64.t) (g1: heap) (g2: heap)
  : Lemma (requires fp_valid fp g1 /\ objects 0UL g2 == objects 0UL g1)
          (ensures fp_valid fp g2)
  = ()

let obj_in_objects_transfer (obj: U64.t) (g1: heap) (g2: heap)
  : Lemma (requires obj_in_objects obj g1 /\ objects 0UL g2 == objects 0UL g1)
          (ensures obj_in_objects obj g2)
  = ()

let obj_in_objects_head (g: heap)
  : Lemma (requires Seq.length (objects 0UL g) > 0 /\ heap_size > 8)
          (ensures obj_in_objects (U64.uint_to_t 8) g)
  = objects_nonempty_head 0UL g;
    Seq.lemma_mem_snoc (Seq.empty #obj_addr) (f_address 0UL);
    assert (Seq.mem (f_address 0UL) (objects 0UL g));
    obj_in_objects_intro (f_address 0UL) g

/// ---------------------------------------------------------------------------
/// Heap density
/// ---------------------------------------------------------------------------

/// The walk from every position where objects > 0 continues at the next position
/// (provided the next position has room for a header), and the head of the next
/// position is in the global objects list.
/// Weakened density: only requires the chain property at positions whose
/// f_address is in objects 0UL g (i.e., actual object header positions).
/// This excludes interior positions of large blocks that have 0UL headers
/// (phantom wosize-0 objects not in the global enumeration).
let heap_objects_dense (g: heap) : prop =
  forall (start: hp_addr).
    U64.v start + 8 < heap_size ==>
    Seq.mem (f_address start) (objects 0UL g) ==>
    Seq.length (objects start g) > 0 ==>
    (let wz = getWosize (read_word g start) in
     let next = U64.v start + ((U64.v wz + 1) * 8) in
     next + 8 < heap_size ==>
     Seq.length (objects (U64.uint_to_t next) g) > 0 /\
     Seq.mem (f_address (U64.uint_to_t next)) (objects 0UL g))

let heap_objects_dense_intro (g: heap)
  : Lemma (requires (forall (start: hp_addr).
                      U64.v start + 8 < heap_size ==>
                      Seq.mem (f_address start) (objects 0UL g) ==>
                      Seq.length (objects start g) > 0 ==>
                      (let wz = getWosize (read_word g start) in
                       let next = U64.v start + ((U64.v wz + 1) * 8) in
                       next + 8 < heap_size ==>
                       Seq.length (objects (U64.uint_to_t next) g) > 0 /\
                       Seq.mem (f_address (U64.uint_to_t next)) (objects 0UL g))))
          (ensures heap_objects_dense g)
  = ()

let objects_dense_step (start: hp_addr) (g: heap)
  : Lemma (requires heap_objects_dense g /\
                    U64.v start + 8 < heap_size /\
                    Seq.mem (f_address start) (objects 0UL g) /\
                    Seq.length (objects start g) > 0)
          (ensures (let wz = getWosize (read_word g start) in
                    let next = U64.v start + ((U64.v wz + 1) * 8) in
                    next + 8 < heap_size ==>
                    Seq.length (objects (U64.uint_to_t next) g) > 0))
  = ()

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let objects_dense_obj_in (start: hp_addr) (g: heap)
  : Lemma (requires heap_objects_dense g /\
                    U64.v start + 8 < heap_size /\
                    Seq.mem (f_address start) (objects 0UL g) /\
                    Seq.length (objects start g) > 0)
          (ensures (let wz = getWosize (read_word g start) in
                    let next = U64.v start + ((U64.v wz + 1) * 8) in
                    next + 8 < heap_size ==>
                    obj_in_objects (U64.uint_to_t (next + 8)) g))
  = let wz = getWosize (read_word g start) in
    let next = U64.v start + ((U64.v wz + 1) * 8) in
    if next + 8 < heap_size then begin
      // From density: mem (f_address next_hp) (objects 0UL g)
      let next_hp : hp_addr = U64.uint_to_t next in
      let oa = f_address next_hp in
      f_address_spec next_hp;
      assert (U64.v oa == next + 8);
      // density gives us Seq.mem oa (objects 0UL g)
      obj_in_objects_intro oa g
    end
#pop-options

/// Transfer: density when objects lists and wosizes agree.
/// The key insight: objects is defined by getWosize(read_word), so equal wosizes
/// mean objects start g2 == objects start g1 for all start. Combined with
/// objects 0UL equality (for global membership), density transfers directly.
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
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
  : Lemma (requires heap_objects_dense g1 /\
                    objects 0UL g2 == objects 0UL g1 /\
                    (forall (p: hp_addr). getWosize (read_word g2 p) == getWosize (read_word g1 p)))
          (ensures heap_objects_dense g2)
  = let aux (start: hp_addr) : Lemma
      (U64.v start + 8 < heap_size ==>
       Seq.mem (f_address start) (objects 0UL g2) ==>
       Seq.length (objects start g2) > 0 ==>
       (let wz = getWosize (read_word g2 start) in
        let next = U64.v start + ((U64.v wz + 1) * 8) in
        next + 8 < heap_size ==>
        Seq.length (objects (U64.uint_to_t next) g2) > 0 /\
        Seq.mem (f_address (U64.uint_to_t next)) (objects 0UL g2)))
    = if U64.v start + 8 < heap_size && Seq.mem (f_address start) (objects 0UL g2) then begin
        // f_address start ∈ objects 0UL g2 == objects 0UL g1
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
#push-options "--z3rlimit 60 --fuel 0 --ifuel 0"
let color_change_preserves_density (obj: obj_addr) (g: heap) (c: color)
  : Lemma (requires heap_objects_dense g)
          (ensures heap_objects_dense (set_object_color obj g c))
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

/// Walk reconstruction: if f_address h ∈ objects 0UL g and wfh g, then objects h g > 0
/// Proof: wfh gives object fits → objects h g is cons oa (...) → length > 0
#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
let member_implies_objects_nonempty (h: hp_addr{U64.v h + 8 < heap_size}) (g: heap)
  : Lemma (requires well_formed_heap g /\
                    Seq.mem (f_address h) (objects 0UL g))
          (ensures Seq.length (objects h g) > 0)
  = let oa : obj_addr = f_address h in
    f_address_spec h;
    // oa = h + 8, oa ∈ objects 0UL g
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

let headers_preserved_from (start: nat) (g_cur g_init: heap) : prop =
  forall (p: hp_addr). U64.v p >= start ==> read_word g_cur p == read_word g_init p

let headers_preserved_from_refl (start: nat) (g: heap)
  : Lemma (ensures headers_preserved_from start g g) = ()

let headers_preserved_from_elim (start: nat) (pos: hp_addr) (g_cur g_init: heap)
  : Lemma (requires headers_preserved_from start g_cur g_init /\ U64.v pos >= start)
          (ensures read_word g_cur pos == read_word g_init pos) = ()

let headers_preserved_from_trans (start1 start2: nat) (g1 g2 g3: heap)
  : Lemma (requires headers_preserved_from start1 g2 g1 /\
                    headers_preserved_from start2 g3 g2 /\
                    start2 >= start1)
          (ensures headers_preserved_from start2 g3 g1) = ()

let headers_preserved_from_write (start: nat) (g: heap) (addr: hp_addr) (v: U64.t)
  : Lemma (requires U64.v addr + U64.v mword <= start)
          (ensures headers_preserved_from start (write_word g addr v) g)
  = let aux (p: hp_addr) : Lemma
      (requires U64.v p >= start)
      (ensures read_word (write_word g addr v) p == read_word g p)
    = read_write_different g addr p v
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

/// ---------------------------------------------------------------------------
/// Whiteness tracking implementation
/// ---------------------------------------------------------------------------

let headers_preserved_before (limit: nat) (g_cur g_init: heap) : prop =
  forall (p: hp_addr). U64.v p < limit ==> read_word g_cur p == read_word g_init p

let headers_preserved_before_refl (limit: nat) (g: heap)
  : Lemma (ensures headers_preserved_before limit g g) = ()

let headers_preserved_before_write (limit: nat) (g: heap) (addr: hp_addr) (v: U64.t)
  : Lemma (requires U64.v addr >= limit)
          (ensures headers_preserved_before limit (write_word g addr v) g)
  = let aux (p: hp_addr) : Lemma
      (requires U64.v p < limit)
      (ensures read_word (write_word g addr v) p == read_word g p)
    = read_write_different g addr p v
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let headers_preserved_before_trans (limit: nat) (g1 g2 g3: heap)
  : Lemma (requires headers_preserved_before limit g2 g1 /\ headers_preserved_before limit g3 g2)
          (ensures headers_preserved_before limit g3 g1) = ()

let headers_preserved_before_weaken (limit1 limit2: nat) (g1 g2: heap)
  : Lemma (requires headers_preserved_before limit2 g2 g1 /\ limit1 <= limit2)
          (ensures headers_preserved_before limit1 g2 g1) = ()

let objects_white_before (pos: nat) (g: heap) : prop =
  forall (x: obj_addr). Seq.mem x (objects 0UL g) ==>
    U64.v (hd_address x) < pos ==> (is_white x g \/ is_blue x g)

let objects_white_before_zero (g: heap)
  : Lemma (ensures objects_white_before 0 g) = ()

let objects_white_before_step (h_addr: hp_addr) (g_pre g_post: heap)
  : Lemma (requires
      objects_white_before (U64.v h_addr) g_pre /\
      objects 0UL g_post == objects 0UL g_pre /\
      well_formed_heap g_post /\
      U64.v h_addr + 8 < heap_size /\
      (is_white (f_address h_addr) g_post \/ is_blue (f_address h_addr) g_post) /\
      headers_preserved_before (U64.v h_addr) g_post g_pre /\
      getWosize (read_word g_post h_addr) == getWosize (read_word g_pre h_addr) /\
      Seq.mem (f_address h_addr) (objects 0UL g_post))
    (ensures objects_white_before 
      (U64.v h_addr + ((U64.v (getWosize (read_word g_pre h_addr)) + 1) * 8)) g_post)
  = let obj : obj_addr = f_address h_addr in
    let wz = getWosize (read_word g_pre h_addr) in
    let next = U64.v h_addr + ((U64.v wz + 1) * 8) in
    GC.Spec.Heap.hd_address_spec obj;
    f_address_spec h_addr;
    assert (U64.v (hd_address obj) = U64.v h_addr);
    let aux (x: obj_addr)
      : Lemma (requires Seq.mem x (objects 0UL g_post) /\ U64.v (hd_address x) < next)
              (ensures is_white x g_post \/ is_blue x g_post)
      = GC.Spec.Heap.hd_address_spec x;
        if U64.v (hd_address x) < U64.v h_addr then begin
          // Case 1: before h_addr — preservation from g_pre
          assert (Seq.mem x (objects 0UL g_pre));
          assert (is_white x g_pre \/ is_blue x g_pre);
          color_of_object_spec x g_pre;
          color_of_object_spec x g_post;
          is_white_iff x g_pre;
          is_white_iff x g_post;
          is_blue_iff x g_pre;
          is_blue_iff x g_post;
          ()
        end
        else if U64.v x = U64.v obj then begin
          FStar.UInt64.v_inj x obj;
          ()
        end
        else if U64.v x > U64.v obj then begin
          assert (U64.v x > U64.v obj);
          objects_separated 0UL g_post obj x;
          wosize_of_object_spec obj g_post;
          assert (U64.v (hd_address obj) = U64.v h_addr);
          assert (wosize_of_object obj g_post == wz);
          assert (U64.v x > U64.v obj + (U64.v wz * 8));
          assert (U64.v (hd_address x) = U64.v x - 8);
          assert (U64.v (hd_address x) > U64.v h_addr + (U64.v wz * 8) - 8 + 8);
          assert false
        end
        else begin
          assert false
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let objects_white_before_all (pos: nat) (g: heap)
  : Lemma (requires objects_white_before pos g /\ pos >= heap_size)
          (ensures forall (x: obj_addr). Seq.mem x (objects 0UL g) ==> (is_white x g \/ is_blue x g))
  = ()

module SpecHeapForExit = GC.Spec.Heap

let objects_white_before_exit (pos: nat) (g: heap)
  : Lemma (requires objects_white_before pos g /\ pos + 8 >= heap_size)
          (ensures forall (x: obj_addr). Seq.mem x (objects 0UL g) ==> (is_white x g \/ is_blue x g))
  = let aux (x: obj_addr)
      : Lemma (requires Seq.mem x (objects 0UL g))
              (ensures is_white x g \/ is_blue x g)
      = SpecHeapForExit.hd_address_bounds x;
        assert (U64.v (hd_address x) + 8 < heap_size);
        assert (U64.v (hd_address x) < pos)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let no_gray_objects (g: heap) : prop =
  forall (obj: obj_addr). Seq.mem obj (objects 0UL g) ==> ~(is_gray obj g)

module SpecHeap = GC.Spec.Heap

#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let no_gray_at_preserved (obj: obj_addr) (g_init g_cur: heap)
  : Lemma (requires no_gray_objects g_init /\
                    Seq.mem obj (objects 0UL g_init) /\
                    read_word g_cur (hd_address obj) == read_word g_init (hd_address obj))
          (ensures ~(is_gray obj g_cur))
  = SpecHeap.hd_address_spec obj;
    color_of_header_eq obj g_cur g_init

let no_gray_elim (obj: obj_addr) (g: heap)
  : Lemma (requires no_gray_objects g /\ Seq.mem obj (objects 0UL g))
          (ensures ~(is_gray obj g))
  = ()
#pop-options

let no_gray_intro (g: heap)
  : Lemma (requires forall (obj: obj_addr). Seq.mem obj (objects 0UL g) ==> ~(is_gray obj g))
          (ensures no_gray_objects g)
  = ()

let set_object_color_headers_preserved_before (h_addr: hp_addr) (obj: obj_addr) (g: heap) (c: color)
  : Lemma (requires hd_address obj == h_addr)
          (ensures headers_preserved_before (U64.v h_addr) (set_object_color obj g c) g)
  = let aux (p: hp_addr) : Lemma
      (requires U64.v p < U64.v h_addr)
      (ensures read_word (set_object_color obj g c) p == read_word g p)
      = set_object_color_read_word obj p g c
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
