(*
   GC.Spec.SweepCoalesce — Fused sweep+coalesce specification (implementation)

   Proves that a single-pass fused sweep+coalesce produces the same result
   as the sequential composition `coalesce(fst(sweep(g, fp)))`.

   Architecture:
   - GC.Spec.SweepCoalesce.Helpers    : bit-level helpers (write_word_id, etc.)
   - GC.Spec.SweepCoalesce.FlushAgree : flush_blue heap-independence
   - GC.Spec.SweepCoalesce.Induction  : core relational induction (combined_proof)
   - GC.Spec.SweepCoalesce            : this file, fused spec + composition theorem
*)
module GC.Spec.SweepCoalesce

open FStar.Seq
open FStar.Mul
module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.SweepCoalesce.Defs

module SpecSweep = GC.Spec.Sweep
module SpecCoalesce = GC.Spec.Coalesce
module HeapGraph = GC.Spec.HeapGraph
module SI = GC.Spec.SweepInv
module Ind = GC.Spec.SweepCoalesce.Induction
module Graph = GC.Spec.Graph

open GC.Spec.Mark
module Header = GC.Lib.Header

/// ---------------------------------------------------------------------------
/// Sweep wosize preservation for ALL objects (not just black)
/// ---------------------------------------------------------------------------

/// Single step: sweep_object preserves wosize of any other object
/// (already public in Sweep: sweep_object_preserves_other_header)
/// Single step: sweep_object preserves its own wosize
/// (already public in Sweep: sweep_object_preserves_self_wosize)

/// Inductive: sweep_aux preserves wosize for ANY member regardless of color
#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
private let rec sweep_aux_preserves_wosize_any
  (g: heap) (objs: seq obj_addr) (fp: U64.t) (x: obj_addr)
  : Lemma (requires well_formed_heap g /\
                    (forall (o: obj_addr). Seq.mem o objs ==> Seq.mem o (objects 0UL g)) /\
                    SpecSweep.fp_in_heap fp g /\
                    Seq.mem x (objects 0UL g) /\
                    Seq.mem x objs /\
                    Graph.is_vertex_set (HeapGraph.coerce_to_vertex_list objs))
          (ensures wosize_of_object x g == wosize_of_object x (fst (SpecSweep.sweep_aux g objs fp)))
          (decreases Seq.length objs)
  = if Seq.length objs = 0 then ()
    else begin
      let obj = Seq.head objs in
      let (g', fp') = SpecSweep.sweep_object g obj fp in
      Seq.lemma_index_is_nth objs 0;
      SpecSweep.sweep_object_preserves_objects g obj fp;
      SpecSweep.sweep_object_preserves_wf g obj fp;
      wf_objects_non_infix g obj;
      HeapGraph.coerce_tail_lemma objs;
      if obj = x then begin
        // x is the current object: use self-preservation
        SpecSweep.sweep_object_preserves_self_wosize g x fp;
        assert (wosize_of_object x g' == wosize_of_object x g);
        // x ∉ tail objs (vertex set: head ∉ tail)
        HeapGraph.coerce_mem_lemma (Seq.tail objs) x;
        assert (~(Seq.mem x (Seq.tail objs)));
        // x still in objects g'
        assert (Seq.mem x (objects 0UL g'));
        // fp' in heap
        (if is_white obj g then () else ());
        assert (SpecSweep.fp_in_heap fp' g');
        // Use nonmember helper for tail
        SpecSweep.sweep_aux_preserves_wosize_nonmember g' (Seq.tail objs) fp' x
      end else begin
        // obj ≠ x: header preserved
        SpecSweep.sweep_object_preserves_other_header g obj fp x;
        assert (wosize_of_object x g' == wosize_of_object x g);
        // x still in objects g' and in tail objs
        assert (Seq.mem x (objects 0UL g'));
        Seq.lemma_mem_inversion objs;
        assert (Seq.mem x (Seq.tail objs));
        // fp' in heap
        (if is_white obj g then () else ());
        assert (SpecSweep.fp_in_heap fp' g');
        // Recurse on tail
        sweep_aux_preserves_wosize_any g' (Seq.tail objs) fp' x
      end
    end
#pop-options

/// Top-level: sweep preserves wosize for ALL objects
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
private let sweep_preserves_wosize_all
  (g: heap) (fp: U64.t) (x: obj_addr)
  : Lemma (requires well_formed_heap g /\
                    noGreyObjects g /\
                    SpecSweep.fp_in_heap fp g /\
                    Seq.mem x (objects 0UL g))
          (ensures wosize_of_object x g == wosize_of_object x (fst (SpecSweep.sweep g fp)))
  = GC.Spec.HeapModel.objects_is_vertex_set g;
    sweep_aux_preserves_wosize_any g (objects 0UL g) fp x
#pop-options

/// ---------------------------------------------------------------------------
/// Color correspondence: is_black x g ↔ ¬(is_blue x gs) for all objects
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
private let sweep_color_correspondence
  (g: heap) (fp: U64.t) (gs: heap) (x: obj_addr)
  : Lemma
    (requires well_formed_heap g /\
              noGreyObjects g /\
              SpecSweep.fp_in_heap fp g /\
              gs == fst (SpecSweep.sweep g fp) /\
              Seq.mem x (objects 0UL g))
    (ensures (is_black x g <==> ~(is_blue x gs)))
  = wf_objects_non_infix g x;
    is_black_iff x g;
    is_white_iff x g;
    is_blue_iff x g;
    is_gray_iff x g;
    if is_black x g then begin
      SpecSweep.sweep_resets_black_to_white g fp;
      assert (is_white x gs);
      is_white_iff x gs;
      is_blue_iff x gs;
      colors_exclusive x gs;
      assert (~(is_blue x gs))
    end else if is_white x g then begin
      SpecSweep.sweep_white_becomes_blue g fp;
      assert (is_blue x gs);
      assert (~(is_black x g))
    end else if is_blue x g then begin
      GC.Spec.HeapModel.objects_is_vertex_set g;
      SpecSweep.sweep_aux_blue_stays_blue g (objects 0UL g) fp x;
      assert (is_blue x gs);
      assert (~(is_black x g))
    end else begin
      // The only remaining case is gray, but precondition says no gray
      // After all iff lemmas, color_of_object is neither Black, White, nor Blue
      // so it must be Gray, meaning is_gray x g = true
      // But noGreyObjects forbids this, giving False
      ()
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Sweep preserves body reads for black objects
/// ---------------------------------------------------------------------------

/// For a black object x, after sweep, read_word at any body address is preserved.
/// This bridges from sweep_aux_preserves_field_member to the condition 7 format.
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
private let sweep_preserves_body_read_black
  (g: heap) (fp: U64.t) (x: obj_addr) (a: hp_addr)
  : Lemma (requires well_formed_heap g /\
                    noGreyObjects g /\
                    SpecSweep.fp_in_heap fp g /\
                    Seq.mem x (objects 0UL g) /\
                    is_black x g /\
                    U64.v a >= U64.v x /\
                    U64.v a + 8 <= U64.v x + U64.v (wosize_of_object x g) * 8)
          (ensures read_word (fst (SpecSweep.sweep g fp)) a == read_word g a)
  = GC.Spec.HeapModel.objects_is_vertex_set g;
    assert (U64.v a < U64.v x + U64.v (wosize_of_object x g) * 8);
    assert (U64.v a % 8 = 0);
    SpecSweep.sweep_aux_preserves_field_member g (objects 0UL g) fp x a
#pop-options

/// ---------------------------------------------------------------------------
/// Objects well-separated and contiguous
/// ---------------------------------------------------------------------------

/// From objects_separated, derive the recursive objs_well_separated predicate
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
private let rec objects_well_separated_lemma
  (start: hp_addr) (g: heap)
  : Lemma (requires Seq.length g == heap_size)
          (ensures Ind.objs_well_separated g (objects start g))
          (decreases Seq.length g - U64.v start)
  = let objs = objects start g in
    if Seq.length objs <= 1 then ()
    else begin
      objects_nonempty_next start g;
      f_address_spec start;
      let wz = getWosize (read_word g start) in
      let next_nat = U64.v start + (U64.v wz + 1) * 8 in
      if next_nat >= heap_size then ()
      else begin
        let next : hp_addr = U64.uint_to_t next_nat in
        // objects start g == cons (f_address start) (objects next g)
        let hd = f_address start in
        // All x in tail (= objects next g) satisfy x > hd + wosize(hd)*8
        let aux (x: obj_addr) : Lemma
          (requires Seq.mem x (Seq.tail objs))
          (ensures U64.v x > U64.v hd + U64.v (wosize_of_object hd g) * 8)
          = objects_separated start g hd x;
            hd_address_spec hd;
            wosize_of_object_spec hd g;
            assert (U64.v (hd_address hd) = U64.v start);
            assert (wosize_of_object hd g == getWosize (read_word g (hd_address hd)));
            assert (wosize_of_object hd g == getWosize (read_word g start));
            assert (wosize_of_object hd g == wz);
            // From mem_cons_lemma: hd is the head of objs, x is in tail = objects next g
            mem_cons_lemma x hd (objects next g); // x ∈ objs
            assert (Seq.mem x objs);
            assert (Seq.mem hd objs);
            if U64.v hd >= U64.v x then begin
              assert (Seq.mem x (Seq.tail objs));
              assert (Seq.equal (Seq.tail objs) (objects next g));
              assert (Seq.mem x (objects next g));
              objects_addresses_gt_start next g x;
              assert (U64.v x > U64.v next);
              assert false
            end else ()
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
        // Recurse on tail
        assert (Seq.equal (Seq.tail objs) (objects next g));
        objects_well_separated_lemma next g;
        assert (Ind.objs_well_separated g (objects next g));
        assert (Ind.objs_well_separated g (Seq.tail objs))
      end
    end
#pop-options

/// From objects walk, derive the recursive objs_contiguous predicate
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
private let rec objects_contiguous_lemma
  (start: hp_addr) (g: heap)
  : Lemma (requires Seq.length g == heap_size)
          (ensures Ind.objs_contiguous g (objects start g))
          (decreases Seq.length g - U64.v start)
  = let objs = objects start g in
    if Seq.length objs <= 1 then ()
    else begin
      objects_nonempty_next start g;
      f_address_spec start;
      let wz = getWosize (read_word g start) in
      let next_nat = U64.v start + (U64.v wz + 1) * 8 in
      if next_nat >= heap_size then ()
      else begin
        let next : hp_addr = U64.uint_to_t next_nat in
        let hd = f_address start in
        // objects start g == cons hd (objects next g)
        // Need: head(tail objs) == hd + (wosize(hd)+1)*8
        // head(tail objs) = head(objects next g) = f_address next = next + 8
        // hd + (wosize(hd)+1)*8 = (start+8) + (wz+1)*8 = start + 8 + wz*8 + 8 = start + (wz+1)*8 + 8 = next + 8
        // Wosize of hd: wosize_of_object hd g = getWosize(read_word g (hd_address hd)) = getWosize(read_word g start) = wz
        hd_address_spec hd;
        wosize_of_object_spec hd g;
        assert (wosize_of_object hd g == wz);
        // tail objs = objects next g, which is nonempty (len objs > 1)
        assert (Seq.length (objects next g) > 0);
        // head(objects next g) = f_address next
        objects_nonempty_next next g;
        f_address_spec next;
        // f_address next = next + 8 = next_nat + 8 = start + (wz+1)*8 + 8
        // hd + (wz+1)*8 = (start+8) + (wz+1)*8 = start + 8 + (wz+1)*8
        assert (U64.v hd + (U64.v wz + 1) * 8 == next_nat + 8);
        assert (U64.v (f_address next) == next_nat + 8);
        // Recurse on tail
        assert (Seq.equal (Seq.tail objs) (objects next g));
        objects_contiguous_lemma next g;
        assert (Ind.objs_contiguous g (objects next g));
        assert (Ind.objs_contiguous g (Seq.tail objs))
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Objects fit in heap
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
private let objects_fit_lemma
  (g: heap) (x: obj_addr)
  : Lemma (requires Seq.mem x (objects 0UL g))
          (ensures U64.v x + U64.v (wosize_of_object x g) * 8 <= heap_size)
  = objects_member_size_bound 0UL g x;
    hd_address_spec x;
    wosize_of_object_spec x g
#pop-options

/// ---------------------------------------------------------------------------
/// Sweep preserves bytes past all objects
/// ---------------------------------------------------------------------------

/// An address past all objects in the heap is not within any object's range
/// (neither header nor body), so sweep_aux doesn't modify it.
#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
private let rec sweep_aux_preserves_past_all
  (g: heap) (objs: seq obj_addr) (fp: U64.t) (a: hp_addr)
  : Lemma (requires well_formed_heap g /\
                    (forall (o: obj_addr). Seq.mem o objs ==> Seq.mem o (objects 0UL g)) /\
                    SpecSweep.fp_in_heap fp g /\
                    (forall (x: obj_addr). Seq.mem x objs ==>
                      U64.v a >= U64.v x + U64.v (wosize_of_object x g) * 8))
          (ensures read_word (fst (SpecSweep.sweep_aux g objs fp)) a == read_word g a)
          (decreases Seq.length objs)
  = if Seq.length objs = 0 then ()
    else begin
      let obj = Seq.head objs in
      let (g', fp') = SpecSweep.sweep_object g obj fp in
      Seq.lemma_index_is_nth objs 0;
      SpecSweep.sweep_object_preserves_objects g obj fp;
      SpecSweep.sweep_object_preserves_wf g obj fp;
      wf_objects_non_infix g obj;
      // a is past obj's body: a >= obj + wosize(obj)*8
      // obj's header is at hd_address(obj) = obj - 8
      // obj's body ranges from obj to obj + wosize(obj)*8 - 8
      // a >= obj + wosize(obj)*8 >= obj > hd_address(obj)
      // So a is not at hd_address(obj) and not in obj's body range
      // sweep_object writes at: hd_address(obj) and possibly obj (if white, set_field 1)
      hd_address_spec obj;
      assert (U64.v a >= U64.v obj + U64.v (wosize_of_object obj g) * 8);
      assert (U64.v (hd_address obj) == U64.v obj - 8);
      // a ≠ hd_address(obj): a >= obj > obj - 8 = hd_address(obj), and both 8-aligned
      assert (U64.v a >= U64.v obj);
      assert (U64.v (hd_address obj) < U64.v obj);
      // a ≠ obj when wosize > 0: a >= obj + wosize*8 >= obj + 8 > obj
      // a ≠ obj when wosize = 0: a >= obj, but sweep_object only writes at obj when wosize > 0
      // In all cases, sweep_object preserves read_word at a
      // We can use sweep_object_preserves_other_body_read if obj ≠ ... but that's for body of x ≠ obj
      // Instead, just unfold sweep_object cases:
      if is_infix obj g then begin
        assert (g' == g);
        assert (fp' == fp)
      end else if is_white obj g then begin
        let ws = wosize_of_object obj g in
        let hd = GC.Spec.Heap.hd_address obj in
        let g_sf =
          if U64.v ws > 0 && U64.v hd + U64.v mword * 2 <= heap_size then begin
            // set_field writes at field 1: addr = hd + mword*1 = obj
            // a >= obj + ws*8 >= obj + 8, so a ≠ obj
            read_write_different g obj a fp;
            HeapGraph.set_field g obj 1UL fp
          end else g
        in
        // makeBlue writes at hd_address(obj)
        // a >= obj > hd_address(obj), so a ≠ hd_address(obj)
        makeBlue_eq obj g_sf;
        color_change_header_locality obj a g_sf Header.Blue;
        assert (read_word g' a == read_word g a)
      end else if is_black obj g then begin
        makeWhite_eq obj g;
        color_change_header_locality obj a g Header.White;
        assert (read_word g' a == read_word g a)
      end else begin
        colors_exclusive obj g;
        assert (g' == g)
      end;
      assert (read_word g' a == read_word g a);
      // For tail: wosize preserved through sweep_object for all objects in tail
      let aux_tail (y: obj_addr)
        : Lemma (requires Seq.mem y (Seq.tail objs))
                (ensures U64.v a >= U64.v y + U64.v (wosize_of_object y g') * 8)
        = assert (Seq.mem y objs);
          assert (U64.v a >= U64.v y + U64.v (wosize_of_object y g) * 8);
          if obj = y then
            SpecSweep.sweep_object_preserves_self_wosize g y fp
          else
            SpecSweep.sweep_object_preserves_other_header g obj fp y;
          assert (wosize_of_object y g' == wosize_of_object y g)
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux_tail);
      // fp' in heap
      (if is_white obj g then () else ());
      // Recurse
      sweep_aux_preserves_past_all g' (Seq.tail objs) fp' a
    end
#pop-options

/// Top-level: sweep preserves bytes past all objects
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
private let sweep_preserves_past_all_objects
  (g: heap) (fp: U64.t) (a: hp_addr)
  : Lemma (requires well_formed_heap g /\
                    noGreyObjects g /\
                    SpecSweep.fp_in_heap fp g /\
                    (forall (x: obj_addr). Seq.mem x (objects 0UL g) ==>
                      U64.v a >= U64.v x + U64.v (wosize_of_object x g) * 8))
          (ensures read_word (fst (SpecSweep.sweep g fp)) a == read_word g a)
  = sweep_aux_preserves_past_all g (objects 0UL g) fp a
#pop-options

/// ---------------------------------------------------------------------------
/// Bridge: getWosize/getTag on read_word for black objects
/// ---------------------------------------------------------------------------

/// For black objects, the header getWosize/getTag are preserved through sweep.
/// This follows from sweep_preserves_wosize_black and sweep_preserves_tag_black.
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
private let sweep_preserves_header_parts_black
  (g: heap) (fp: U64.t) (gs: heap) (x: obj_addr)
  : Lemma (requires well_formed_heap g /\
                    noGreyObjects g /\
                    SpecSweep.fp_in_heap fp g /\
                    gs == fst (SpecSweep.sweep g fp) /\
                    Seq.mem x (objects 0UL g) /\
                    is_black x g)
          (ensures getWosize (read_word g (hd_address x)) == getWosize (read_word gs (hd_address x)) /\
                   getTag (read_word g (hd_address x)) == getTag (read_word gs (hd_address x)))
  = SpecSweep.sweep_preserves_wosize_black g fp x;
    SpecSweep.sweep_preserves_tag_black g fp x;
    wosize_of_object_spec x g;
    wosize_of_object_spec x gs;
    tag_of_object_spec x g;
    tag_of_object_spec x gs
#pop-options

/// ---------------------------------------------------------------------------
/// Main composition theorem
/// ---------------------------------------------------------------------------

/// The proof instantiates combined_proof with:
///   h_f = g, h_c = gs, objs = objects 0UL g, fb = 0UL, rw = 0, fp = 0UL
/// where gs = fst (sweep g fp).

#push-options "--z3rlimit 400 --fuel 2 --ifuel 1 --split_queries always"
let fused_eq_sweep_coalesce (g: heap) (fp: U64.t)
  : Lemma
    (requires well_formed_heap g /\
              SI.heap_objects_dense g /\
              SpecSweep.fp_in_heap fp g /\
              (forall (x: obj_addr). Seq.mem x (objects 0UL g) ==>
                ~(is_gray x g)))
    (ensures fused_sweep_coalesce g ==
             SpecCoalesce.coalesce (fst (SpecSweep.sweep g fp)))
  =
  let gs = fst (SpecSweep.sweep g fp) in
  let objs = objects 0UL g in

  // Establish gs properties
  SpecSweep.sweep_preserves_objects g fp;
  assert (objects 0UL gs == objs);
  SpecSweep.sweep_preserves_wf g fp;
  assert (well_formed_heap gs);

  // === Condition 1: Sizes ===
  // g: heap and gs: heap both have length == heap_size by type refinement
  assert (Seq.length g == heap_size);
  assert (Seq.length gs == heap_size);

  // === Condition 2: Color correspondence ===
  let cond2_aux (x: obj_addr)
    : Lemma (requires Seq.mem x objs)
            (ensures (is_black x g <==> ~(is_blue x gs)))
    = sweep_color_correspondence g fp gs x
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires cond2_aux);

  // === Condition 3: Wosize correspondence ===
  let cond3_aux (x: obj_addr)
    : Lemma (requires Seq.mem x objs)
            (ensures wosize_of_object x g == wosize_of_object x gs)
    = sweep_preserves_wosize_all g fp x
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires cond3_aux);

  // === Condition 4: Agree below bound ===
  // With rw=0, bound = if len objs > 0 then hd_address(head objs) else heap_size
  // Case 1: objs nonempty → head objs = f_address 0UL = 8UL, hd_address 8UL = 0UL, bound=0 → vacuous
  // Case 2: objs empty → bound = heap_size → need all reads to agree
  //   But when objs is empty, sweep_aux does nothing, so g == gs anyway
  let cond4 : squash (let bound = if 0 > 0 then U64.v 0UL - 8
                      else if Seq.length objs > 0 then U64.v (hd_address (Seq.head objs))
                      else heap_size in
          forall (a: hp_addr). U64.v a + 8 <= bound ==> read_word g a == read_word gs a)
    = if Seq.length objs > 0 then begin
        objects_nonempty_head 0UL g;
        f_address_spec 0UL;
        hd_address_spec (f_address 0UL)
        // bound = 0, vacuously true
      end else begin
        // objs = objects 0UL g is empty, so sweep_aux g objs fp = (g, fp)
        // meaning gs = g and all reads agree trivially
        assert (Seq.length objs = 0);
        // sweep g fp = sweep_aux g (objects 0UL g) fp = sweep_aux g objs fp
        // When objs is empty, sweep_aux g Seq.empty fp = (g, fp) by definition
        // So gs = fst (sweep g fp) = fst (sweep_aux g objs fp) = g
        ()
      end
  in

  // === Condition 5: Agree above ===
  // With rw=0, the condition simplifies to:
  //   forall a. (forall x ∈ objs. a >= x + wosize(x)*8) ==> read_word g a == read_word gs a
  let cond5_aux (a: hp_addr)
    : Lemma (requires (forall (x: obj_addr). Seq.mem x objs ==>
                        U64.v a >= U64.v x + U64.v (wosize_of_object x g) * 8))
            (ensures read_word g a == read_word gs a)
    = sweep_preserves_past_all_objects g fp a
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires cond5_aux);

  // === Condition 6: Black header wosize/tag match ===
  let cond6_aux (x: obj_addr)
    : Lemma (requires Seq.mem x objs /\ is_black x g)
            (ensures getWosize (read_word g (hd_address x)) == getWosize (read_word gs (hd_address x)) /\
                     getTag (read_word g (hd_address x)) == getTag (read_word gs (hd_address x)))
    = sweep_preserves_header_parts_black g fp gs x
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires cond6_aux);

  // === Condition 7: Black bodies agree ===
  let cond7_aux (x: obj_addr)
    : Lemma (requires Seq.mem x objs /\ is_black x g)
            (ensures forall (a: hp_addr).
              U64.v a >= U64.v x /\ U64.v a + 8 <= U64.v x + U64.v (wosize_of_object x g) * 8 ==>
              read_word g a == read_word gs a)
    = let body_aux (a: hp_addr)
        : Lemma (requires U64.v a >= U64.v x /\ U64.v a + 8 <= U64.v x + U64.v (wosize_of_object x g) * 8)
                (ensures read_word g a == read_word gs a)
        = sweep_preserves_body_read_black g fp x a
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires body_aux)
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires cond7_aux);

  // === Condition 8: Black objects white in gs ===
  SpecSweep.sweep_resets_black_to_white g fp;

  // === Condition 9: Geometric — vacuously true (rw=0) ===
  // === Condition 10: fb validity — vacuously true (rw=0) ===

  // === Condition 11: Well-separated ===
  objects_well_separated_lemma 0UL g;

  // === Condition 12: Contiguous ===
  objects_contiguous_lemma 0UL g;

  // === Condition 13: Run-object contiguity — vacuously true (rw=0) ===

  // === Condition 14: Objects fit ===
  let cond14_aux (x: obj_addr)
    : Lemma (requires Seq.mem x objs)
            (ensures U64.v x + U64.v (wosize_of_object x g) * 8 <= heap_size)
    = objects_fit_lemma g x
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires cond14_aux);

  // === Apply combined_proof ===
  // Instantiate: h_f = g, h_c = gs, objs = objects 0UL g, fb = 0UL, rw = 0, fp = 0UL
  Ind.combined_proof g gs g gs objs 0UL 0 0UL;
  // This gives: fused_aux g g objs 0UL 0 0UL == coalesce_aux gs gs objs 0UL 0 0UL
  assert (fused_aux g g objs 0UL 0 0UL == SpecCoalesce.coalesce_aux gs gs objs 0UL 0 0UL);

  // LHS: fused_sweep_coalesce g = fused_aux g g (objects 0UL g) 0UL 0 0UL  (by definition)

  // RHS: coalesce gs = coalesce_aux gs gs (objects 0UL gs) 0UL 0 0UL  (by definition)
  //     = coalesce_aux gs gs (objects 0UL g) 0UL 0 0UL   (since objects 0UL gs == objects 0UL g)
  //     = coalesce_aux gs gs objs 0UL 0 0UL
  assert (SpecCoalesce.coalesce gs == SpecCoalesce.coalesce_aux gs gs (objects 0UL gs) 0UL 0 0UL);
  assert (objects 0UL gs == objs);
  assert (SpecCoalesce.coalesce gs == SpecCoalesce.coalesce_aux gs gs objs 0UL 0 0UL);

  // Conclude
  assert (fused_sweep_coalesce g == SpecCoalesce.coalesce gs)
#pop-options
