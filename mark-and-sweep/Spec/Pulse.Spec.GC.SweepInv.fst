/// ---------------------------------------------------------------------------
/// Pulse.Spec.GC.SweepInv - Implementation
/// ---------------------------------------------------------------------------

module Pulse.Spec.GC.SweepInv

open FStar.Seq
open Pulse.Spec.GC.Base
open Pulse.Spec.GC.Heap
open Pulse.Spec.GC.Object
open Pulse.Spec.GC.Fields
open Pulse.Spec.GC.HeapGraph

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
    Seq.lemma_mem_snoc (Seq.empty #obj_addr) (obj_address 0UL);
    assert (Seq.mem (obj_address 0UL) (objects 0UL g));
    obj_in_objects_intro (obj_address 0UL) g

/// ---------------------------------------------------------------------------
/// Heap density
/// ---------------------------------------------------------------------------

/// The walk from every position where objects > 0 continues at the next position
/// (provided the next position has room for a header), and the head of the next
/// position is in the global objects list.
let heap_objects_dense (g: heap) : prop =
  forall (start: hp_addr).
    Seq.length (objects start g) > 0 ==>
    (let wz = getWosize (read_word g start) in
     let next = U64.v start + FStar.Mul.((U64.v wz + 1) * 8) in
     next + 8 < heap_size ==>
     Seq.length (objects (U64.uint_to_t next) g) > 0 /\
     Seq.mem (obj_address (U64.uint_to_t next)) (objects 0UL g))

let objects_dense_step (start: hp_addr) (g: heap)
  : Lemma (requires heap_objects_dense g /\ Seq.length (objects start g) > 0)
          (ensures (let wz = getWosize (read_word g start) in
                    let next = U64.v start + FStar.Mul.((U64.v wz + 1) * 8) in
                    next + 8 < heap_size ==>
                    Seq.length (objects (U64.uint_to_t next) g) > 0))
  = ()

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let objects_dense_obj_in (start: hp_addr) (g: heap)
  : Lemma (requires heap_objects_dense g /\ Seq.length (objects start g) > 0)
          (ensures (let wz = getWosize (read_word g start) in
                    let next = U64.v start + FStar.Mul.((U64.v wz + 1) * 8) in
                    next + 8 < heap_size ==>
                    obj_in_objects (U64.uint_to_t (next + 8)) g))
  = let wz = getWosize (read_word g start) in
    let next = U64.v start + FStar.Mul.((U64.v wz + 1) * 8) in
    if next + 8 < heap_size then begin
      // From density: mem (obj_address next_hp) (objects 0UL g)
      let next_hp : hp_addr = U64.uint_to_t next in
      let oa = obj_address next_hp in
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
      let next = U64.v start + FStar.Mul.((U64.v wz1 + 1) * 8) in
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
      (Seq.length (objects start g2) > 0 ==>
       (let wz = getWosize (read_word g2 start) in
        let next = U64.v start + FStar.Mul.((U64.v wz + 1) * 8) in
        next + 8 < heap_size ==>
        Seq.length (objects (U64.uint_to_t next) g2) > 0 /\
        Seq.mem (obj_address (U64.uint_to_t next)) (objects 0UL g2)))
    = objects_eq_from_wosize start g1 g2;
      if Seq.length (objects start g2) > 0 then begin
        let wz = getWosize (read_word g2 start) in
        assert (wz == getWosize (read_word g1 start));
        let next = U64.v start + FStar.Mul.((U64.v wz + 1) * 8) in
        if next + 8 < heap_size then begin
          objects_eq_from_wosize (U64.uint_to_t next) g1 g2
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

/// Walk reconstruction: if obj_address h ∈ objects 0UL g and wfh g, then objects h g > 0
/// Proof: wfh gives object fits → objects h g is cons oa (...) → length > 0
#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
let member_implies_objects_nonempty (h: hp_addr{U64.v h + 8 < heap_size}) (g: heap)
  : Lemma (requires well_formed_heap g /\
                    Seq.mem (obj_address h) (objects 0UL g))
          (ensures Seq.length (objects h g) > 0)
  = let oa : obj_addr = obj_address h in
    // oa = h + 8, oa ∈ objects 0UL g
    // From well_formed_heap: hd_address oa + 8 + wz*8 <= Seq.length g
    Pulse.Spec.GC.Heap.hd_address_spec oa;
    Pulse.Spec.GC.Object.wosize_of_object_spec oa g;
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

let objects_white_before (pos: nat) (g: heap) : prop =
  forall (x: obj_addr). Seq.mem x (objects 0UL g) ==>
    U64.v (hd_address x) < pos ==> is_white x g

let objects_white_before_zero (g: heap)
  : Lemma (ensures objects_white_before 0 g) = ()

let objects_white_before_step (h_addr: hp_addr) (g_pre g_post: heap)
  : Lemma (requires
      objects_white_before (U64.v h_addr) g_pre /\
      objects 0UL g_post == objects 0UL g_pre /\
      well_formed_heap g_post /\
      U64.v h_addr + 8 < heap_size /\
      is_white (obj_address h_addr) g_post /\
      headers_preserved_before (U64.v h_addr) g_post g_pre /\
      getWosize (read_word g_post h_addr) == getWosize (read_word g_pre h_addr) /\
      Seq.mem (obj_address h_addr) (objects 0UL g_post))
    (ensures objects_white_before 
      (U64.v h_addr + FStar.Mul.((U64.v (getWosize (read_word g_pre h_addr)) + 1) * 8)) g_post)
  = let obj : obj_addr = obj_address h_addr in
    let wz = getWosize (read_word g_pre h_addr) in
    let next = U64.v h_addr + FStar.Mul.((U64.v wz + 1) * 8) in
    Pulse.Spec.GC.Heap.hd_address_spec obj;
    assert (U64.v (hd_address obj) = U64.v h_addr);
    let aux (x: obj_addr)
      : Lemma (requires Seq.mem x (objects 0UL g_post) /\ U64.v (hd_address x) < next)
              (ensures is_white x g_post)
      = Pulse.Spec.GC.Heap.hd_address_spec x;
        if U64.v (hd_address x) < U64.v h_addr then begin
          // Case 1: before h_addr — preservation from g_pre
          // headers_preserved_before gives read_word equality
          assert (Seq.mem x (objects 0UL g_pre));
          // From objects_white_before in g_pre:
          assert (is_white x g_pre);
          // Bridge via color_of_object_spec:
          color_of_object_spec x g_pre;
          color_of_object_spec x g_post;
          is_white_iff x g_pre;
          is_white_iff x g_post;
          ()
        end
        else if U64.v x = U64.v obj then begin
          // Case 2: x == obj_address h_addr
          FStar.UInt64.v_inj x obj;
          ()
        end
        else if U64.v x > U64.v obj then begin
          // Case 3: x > obj — use objects_separated to get contradiction
          assert (U64.v x > U64.v obj);
          objects_separated 0UL g_post obj x;
          // objects_separated: U64.v x > U64.v obj + wosize_of_object_as_wosize(obj, g_post) * 8
          wosize_of_object_spec obj g_post;
          assert (U64.v (hd_address obj) = U64.v h_addr);
          // wosize_of_object obj g_post = getWosize(read_word g_post (hd_address obj))
          //                              = getWosize(read_word g_post h_addr)
          //                              = getWosize(read_word g_pre h_addr) = wz
          assert (wosize_of_object obj g_post == wz);
          // So: U64.v x > U64.v obj + wz * 8 = h_addr + 8 + wz * 8
          // hd_address x = x - 8 > h_addr + wz * 8
          // Both h_addr and hd_address x are 8-aligned, wz*8 is 8-aligned
          // So hd_address x >= h_addr + wz * 8 + 8 = h_addr + (wz+1)*8 = next
          // This contradicts hd_address x < next
          assert (U64.v x > U64.v obj + FStar.Mul.(U64.v wz * 8));
          assert (U64.v (hd_address x) = U64.v x - 8);
          assert (U64.v (hd_address x) > U64.v h_addr + FStar.Mul.(U64.v wz * 8) - 8 + 8);
          // hd_address x is a multiple of 8 (from hp_addr/obj_addr alignment)
          // h_addr + wz*8 is a multiple of 8
          // hd_address x > h_addr + wz*8 and both multiples of 8
          // => hd_address x >= h_addr + wz*8 + 8 = next
          assert false
        end
        else begin
          // Case 4: x < obj but hd_address x >= h_addr
          // x < obj = h_addr + 8 and hd_address x = x - 8 >= h_addr
          // => x >= h_addr + 8 and x < h_addr + 8 => contradiction
          assert false
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let objects_white_before_all (pos: nat) (g: heap)
  : Lemma (requires objects_white_before pos g /\ pos >= heap_size)
          (ensures forall (x: obj_addr). Seq.mem x (objects 0UL g) ==> is_white x g)
  = ()

let no_gray_objects (g: heap) : prop =
  forall (obj: obj_addr). Seq.mem obj (objects 0UL g) ==> ~(is_gray obj g)

#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"
let no_gray_at_preserved (obj: obj_addr) (g_init g_cur: heap)
  : Lemma (requires no_gray_objects g_init /\
                    Seq.mem obj (objects 0UL g_init) /\
                    read_word g_cur (hd_address obj) == read_word g_init (hd_address obj))
          (ensures ~(is_gray obj g_cur))
  = color_of_object_spec obj g_init;
    color_of_object_spec obj g_cur;
    // Now: color_of_object obj g_init == getColor (read_word g_init (hd_address obj))
    //      color_of_object obj g_cur  == getColor (read_word g_cur  (hd_address obj))
    // With read_word g_cur _ == read_word g_init _, by congruence:
    //      color_of_object obj g_cur == color_of_object obj g_init
    is_gray_iff obj g_init;
    is_gray_iff obj g_cur;
    // is_gray obj g <==> color_of_object obj g = Gray
    // no_gray_objects gives ~(is_gray obj g_init)
    // therefore color_of_object obj g_init <> Gray
    // therefore color_of_object obj g_cur <> Gray
    // therefore ~(is_gray obj g_cur)
    // Help SMT see the connection:
    let c_init = color_of_object obj g_init in
    let c_cur = color_of_object obj g_cur in
    assert (c_init == getColor (read_word g_init (hd_address obj)));
    ()
#pop-options

let no_gray_intro (g: heap)
  : Lemma (requires forall (obj: obj_addr). Seq.mem obj (objects 0UL g) ==> ~(is_gray obj g))
          (ensures no_gray_objects g)
  = ()
