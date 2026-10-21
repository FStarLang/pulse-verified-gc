(*
   GC.Spec.FreeList.Sweep — sweep preserves free-list exactness.

   `sweep_object` prepends each newly-freed (white) block to the free list and
   leaves already-blue blocks alone, so exactness is a *preservation* property:
   if the free list is exactly the blue set before the step, it is exactly the
   blue set after it.  Lifting the step lemma over `sweep_aux` gives the same
   statement for the whole sweep phase.
*)
module GC.Spec.FreeList.Sweep

open FStar.Seq

module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Mark
open GC.Spec.Sweep
open GC.Spec.FreeList

/// ---------------------------------------------------------------------------
/// The chain is untouched by a step on a non-blue object
/// ---------------------------------------------------------------------------

/// Every cell of the chain is blue, so a step that processes a non-blue object
/// never writes a cell's link word: the only writes are to the object's own
/// header and its own field 1, and the object is not a cell.
#push-options "--z3rlimit 15 --fuel 2 --ifuel 1"
let rec sweep_object_preserves_chain
  (g: heap) (obj: obj_addr) (fp: U64.t) (head: U64.t) (x: U64.t) (n: nat)
  : Lemma (requires well_formed_heap g /\ Seq.mem obj (objects zero_addr g) /\ fp_in_heap fp g /\
                    fl_sound g head /\ ~(is_blue obj g))
          (ensures on_fl (fst (sweep_object g obj fp)) head x n == on_fl g head x n)
          (decreases n)
  = let g' = fst (sweep_object g obj fp) in
    if n = 0 then ()
    else if not (fl_node head) then ()
    else if head = x then ()
    else begin
      // `head` lies on its own chain, so soundness makes it a blue heap object
      reachable_head g head;
      assert (Seq.mem (head <: obj_addr) (objects zero_addr g));
      assert (is_blue (head <: obj_addr) g);
      assert ((head <: obj_addr) <> obj);
      // its link word sits at `head`, inside its own body since wosize >= 1
      assert (U64.v (wosize_of_object (head <: obj_addr) g) >= 1);
      sweep_object_preserves_other_body_read g obj fp (head <: obj_addr) (head <: hp_addr);
      assert (fl_next g' head == fl_next g head);
      fl_sound_tail g head;
      sweep_object_preserves_chain g obj fp (fl_next g head) x (n - 1)
    end
#pop-options

let sweep_object_preserves_reachable
  (g: heap) (obj: obj_addr) (fp: U64.t) (head: U64.t) (x: U64.t)
  : Lemma (requires well_formed_heap g /\ Seq.mem obj (objects zero_addr g) /\ fp_in_heap fp g /\
                    fl_sound g head /\ ~(is_blue obj g))
          (ensures reachable_on_fl (fst (sweep_object g obj fp)) head x <==>
                   reachable_on_fl g head x)
  = let g' = fst (sweep_object g obj fp) in
    introduce reachable_on_fl g head x ==> reachable_on_fl g' head x
    with (eliminate exists (n: nat). on_fl g head x n
          with (sweep_object_preserves_chain g obj fp head x n;
                assert (on_fl g' head x n)));
    introduce reachable_on_fl g' head x ==> reachable_on_fl g head x
    with (eliminate exists (n: nat). on_fl g' head x n
          with (sweep_object_preserves_chain g obj fp head x n;
                assert (on_fl g head x n)))

/// ---------------------------------------------------------------------------
/// One sweep step preserves exactness
/// ---------------------------------------------------------------------------

/// The white case: `obj` is freed, made blue, and pushed onto the head of the
/// list with its link pointing at the old head.
#push-options "--z3rlimit 300 --fuel 2 --ifuel 1"
private let sweep_object_white_preserves_fl_exact
  (g: heap) (obj: obj_addr) (fp: U64.t)
  : Lemma (requires well_formed_heap g /\ Seq.mem obj (objects zero_addr g) /\ fp_in_heap fp g /\
                    fl_exact g fp /\ is_white obj g)
          (ensures (let (g', fp') = sweep_object g obj fp in fl_exact g' fp'))
  = wf_objects_non_infix g obj;
    colors_exclusive obj g;
    sweep_object_preserves_objects g obj fp;
    hd_address_spec obj;
    let ws = wosize_of_object obj g in
    let hd = GC.Spec.Heap.hd_address obj in
    // `wf_object_bound` gives obj + wosize*8 <= heap_size, i.e.
    // hd + (wosize+1)*8 <= heap_size, so at wosize >= 1 the room for a link
    // word is automatic. The else branch below is therefore exactly wosize 0.
    wf_object_bound g obj;
    if U64.v ws > 0 && U64.v hd + U64.v mword * 2 <= heap_size then begin
      let g' = fst (sweep_object g obj fp) in
      assert (snd (sweep_object g obj fp) == obj);
      // the new head links to the old head
      sweep_object_white_field0 g obj fp;
      assert (fl_next g' obj == fp);
      sweep_object_resets_self_color g obj fp;
      assert (is_blue obj g');
      sweep_object_preserves_self_wosize g obj fp;
      assert (U64.v (wosize_of_object obj g') >= 1);
      // soundness
      introduce forall (y: U64.t). reachable_on_fl g' obj y ==>
        (fl_node y /\
         (U64.v y >= U64.v mword /\ U64.v y < heap_size /\ U64.v y % U64.v mword == 0) /\
         Seq.mem (y <: obj_addr) (objects zero_addr g') /\
         is_blue (y <: obj_addr) g' /\
         U64.v (wosize_of_object (y <: obj_addr) g') >= 1)
      with introduce _ ==> _
      with begin
        reachable_is_node g' obj y;
        if y = obj then ()
        else begin
          reachable_uncons g' obj y;
          sweep_object_preserves_reachable g obj fp fp y;
          assert (reachable_on_fl g fp y);
          assert (is_blue (y <: obj_addr) g);
          assert (U64.v (wosize_of_object (y <: obj_addr) g) >= 1);
          sweep_object_color_locality g obj (y <: obj_addr) fp;
          sweep_object_preserves_other_header g obj fp (y <: obj_addr);
          is_blue_iff (y <: obj_addr) g;
          is_blue_iff (y <: obj_addr) g'
        end
      end;
      // completeness
      introduce forall (y: obj_addr). (Seq.mem y (objects zero_addr g') /\ is_blue y g'
                                       /\ U64.v (wosize_of_object y g') >= 1) ==>
                                      reachable_on_fl g' obj y
      with introduce _ ==> _
      with begin
        if y = obj then reachable_head g' obj
        else begin
          sweep_object_color_locality g obj y fp;
          sweep_object_preserves_other_header g obj fp y;
          is_blue_iff y g;
          is_blue_iff y g';
          assert (is_blue y g);
          assert (U64.v (wosize_of_object y g) >= 1);
          assert (reachable_on_fl g fp y);
          sweep_object_preserves_reachable g obj fp fp y;
          reachable_cons g' obj y
        end
      end
    end
    else begin
      // wosize 0: the block cannot hold a link, so `sweep_object` colours it
      // blue and leaves the list alone. The chain is untouched, and the new
      // blue block is not a cell, so completeness does not reach for it.
      let g' = fst (sweep_object g obj fp) in
      assert (snd (sweep_object g obj fp) == fp);
      sweep_object_resets_self_color g obj fp;
      sweep_object_preserves_self_wosize g obj fp;
      assert (U64.v (wosize_of_object obj g') == 0);
      // soundness: the chain is the same chain, and its members keep their
      // colour and their header, because none of them is `obj`.
      introduce forall (y: U64.t). reachable_on_fl g' fp y ==>
        (fl_node y /\
         (U64.v y >= U64.v mword /\ U64.v y < heap_size /\ U64.v y % U64.v mword == 0) /\
         Seq.mem (y <: obj_addr) (objects zero_addr g') /\
         is_blue (y <: obj_addr) g' /\
         U64.v (wosize_of_object (y <: obj_addr) g') >= 1)
      with introduce _ ==> _
      with begin
        sweep_object_preserves_reachable g obj fp fp y;
        assert (reachable_on_fl g fp y);
        assert (is_blue (y <: obj_addr) g);
        // y is blue in g and obj is white in g, so they are distinct
        is_blue_iff (y <: obj_addr) g;
        is_white_iff obj g;
        assert ((y <: obj_addr) <> obj);
        sweep_object_color_locality g obj (y <: obj_addr) fp;
        sweep_object_preserves_other_header g obj fp (y <: obj_addr);
        is_blue_iff (y <: obj_addr) g;
        is_blue_iff (y <: obj_addr) g'
      end;
      // completeness: obj is blue in g' but has wosize 0, so it is excluded.
      introduce forall (y: obj_addr). (Seq.mem y (objects zero_addr g') /\ is_blue y g'
                                       /\ U64.v (wosize_of_object y g') >= 1) ==>
                                      reachable_on_fl g' fp y
      with introduce _ ==> _
      with begin
        assert (Seq.mem y (objects zero_addr g));
        // y cannot be obj: obj has wosize 0 in g', and the hypothesis of this
        // implication demands wosize >= 1, so that case is vacuous.
        if y = obj then ()
        else begin
          sweep_object_color_locality g obj y fp;
          sweep_object_preserves_other_header g obj fp y;
          is_blue_iff y g;
          is_blue_iff y g';
          assert (is_blue y g);
          assert (U64.v (wosize_of_object y g) >= 1);
          fl_complete_elim g fp y;
          assert (reachable_on_fl g fp y);
          sweep_object_preserves_reachable g obj fp fp y
        end
      end
    end
#pop-options

/// The black case: `obj` is recycled to white; the list is untouched.
#push-options "--z3rlimit 37 --fuel 2 --ifuel 1"
private let sweep_object_black_preserves_fl_exact
  (g: heap) (obj: obj_addr) (fp: U64.t)
  : Lemma (requires well_formed_heap g /\ Seq.mem obj (objects zero_addr g) /\ fp_in_heap fp g /\
                    fl_exact g fp /\ is_black obj g)
          (ensures (let (g', fp') = sweep_object g obj fp in fl_exact g' fp'))
  = wf_objects_non_infix g obj;
    colors_exclusive obj g;
    sweep_object_preserves_objects g obj fp;
    let g' = fst (sweep_object g obj fp) in
    assert (snd (sweep_object g obj fp) == fp);
    sweep_object_resets_self_color g obj fp;
    assert (is_white obj g');
    colors_exclusive obj g';
    assert (~(is_blue obj g'));
    // soundness
    introduce forall (y: U64.t). reachable_on_fl g' fp y ==>
      (fl_node y /\
       (U64.v y >= U64.v mword /\ U64.v y < heap_size /\ U64.v y % U64.v mword == 0) /\
       Seq.mem (y <: obj_addr) (objects zero_addr g') /\
       is_blue (y <: obj_addr) g' /\
       U64.v (wosize_of_object (y <: obj_addr) g') >= 1)
    with introduce _ ==> _
    with begin
      reachable_is_node g' fp y;
      sweep_object_preserves_reachable g obj fp fp y;
      assert (reachable_on_fl g fp y);
      assert (is_blue (y <: obj_addr) g);
      assert ((y <: obj_addr) <> obj);
      sweep_object_color_locality g obj (y <: obj_addr) fp;
      sweep_object_preserves_other_header g obj fp (y <: obj_addr);
      is_blue_iff (y <: obj_addr) g;
      is_blue_iff (y <: obj_addr) g'
    end;
    // completeness
    introduce forall (y: obj_addr). (Seq.mem y (objects zero_addr g') /\ is_blue y g'
                                     /\ U64.v (wosize_of_object y g') >= 1) ==>
                                    reachable_on_fl g' fp y
    with introduce _ ==> _
    with begin
      assert (y <> obj);
      sweep_object_color_locality g obj y fp;
      sweep_object_preserves_other_header g obj fp y;
      is_blue_iff y g;
      is_blue_iff y g';
      assert (is_blue y g);
      assert (U64.v (wosize_of_object y g) >= 1);
      fl_complete_elim g fp y;
      assert (reachable_on_fl g fp y);
      sweep_object_preserves_reachable g obj fp fp y
    end
#pop-options

/// A sweep step preserves free-list exactness.
#push-options "--z3rlimit 25 --fuel 2 --ifuel 1"
let sweep_object_preserves_fl_exact (g: heap) (obj: obj_addr) (fp: U64.t)
  : Lemma (requires well_formed_heap g /\ Seq.mem obj (objects zero_addr g) /\ fp_in_heap fp g /\
                    fl_exact g fp)
          (ensures (let (g', fp') = sweep_object g obj fp in fl_exact g' fp'))
  = wf_objects_non_infix g obj;
    if is_white obj g then sweep_object_white_preserves_fl_exact g obj fp
    else if is_black obj g then sweep_object_black_preserves_fl_exact g obj fp
    else ()   // blue or gray: the step is the identity
#pop-options

/// ---------------------------------------------------------------------------
/// Side conditions are preserved, so the induction goes through
/// ---------------------------------------------------------------------------

/// The updated free pointer is still a heap object (or null).
#push-options "--z3rlimit 25 --fuel 2 --ifuel 1"
let sweep_object_preserves_fp_in_heap (g: heap) (obj: obj_addr) (fp: U64.t)
  : Lemma (requires well_formed_heap g /\ Seq.mem obj (objects zero_addr g) /\ fp_in_heap fp g)
          (ensures (let (g', fp') = sweep_object g obj fp in fp_in_heap fp' g'))
  = sweep_object_preserves_objects g obj fp
#pop-options

/// ---------------------------------------------------------------------------
/// The whole sweep phase preserves exactness
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let rec sweep_aux_preserves_fl_exact
  (g: heap) (objs: seq obj_addr) (fp: U64.t)
  : Lemma (requires well_formed_heap g /\ fp_in_heap fp g /\
                    (forall (o: obj_addr). Seq.mem o objs ==> Seq.mem o (objects zero_addr g)) /\
                    fl_exact g fp)
          (ensures (let (g', fp') = sweep_aux g objs fp in fl_exact g' fp'))
          (decreases Seq.length objs)
  = if Seq.length objs = 0 then ()
    else begin
      let obj = Seq.head objs in
      Seq.lemma_index_is_nth objs 0;
      assert (Seq.mem obj objs);
      let (g', fp') = sweep_object g obj fp in
      sweep_object_preserves_objects g obj fp;
      sweep_object_preserves_wf g obj fp;
      sweep_object_preserves_fp_in_heap g obj fp;
      sweep_object_preserves_fl_exact g obj fp;
      Seq.lemma_mem_inversion objs;
      sweep_aux_preserves_fl_exact g' (Seq.tail objs) fp'
    end
#pop-options

/// **Free-list exactness is preserved by the sweep phase.**
///
/// After sweeping, the objects reachable along the free list from the returned
/// free pointer are *exactly* the blue objects of the heap: nothing live is on
/// the list (soundness) and no free block is stranded off it (completeness).
let sweep_preserves_fl_exact (g: heap) (fp: U64.t)
  : Lemma (requires well_formed_heap g /\ fp_in_heap fp g /\
                    fl_exact g fp)
          (ensures (let (g', fp') = sweep g fp in fl_exact g' fp'))
  = sweep_aux_preserves_fl_exact g (objects zero_addr g) fp

/// ---------------------------------------------------------------------------
/// Establishing the invariant
/// ---------------------------------------------------------------------------
///
/// Preservation alone would be worthless if the invariant were unreachable, so
/// we also show it holds of the state the collector actually starts from: a
/// heap with no free blocks and a null free pointer.

/// A null free pointer is exact exactly when the heap has no blue objects.
let fl_exact_null (g: heap)
  : Lemma (requires (forall (obj: obj_addr). Seq.mem obj (objects zero_addr g) ==> ~(is_blue obj g)))
          (ensures fl_exact g 0UL)
  = assert (~(fl_node 0UL));
    introduce forall (y: U64.t) (n: nat). ~(on_fl g 0UL y n)
    with ()

/// Sweeping a heap that has no free blocks *establishes* exactness.
let sweep_establishes_fl_exact (g: heap)
  : Lemma (requires well_formed_heap g /\                     (forall (obj: obj_addr). Seq.mem obj (objects zero_addr g) ==> ~(is_blue obj g)))
          (ensures (let (g', fp') = sweep g 0UL in fl_exact g' fp'))
  = fl_exact_null g;
    assert (fp_in_heap 0UL g);
    sweep_preserves_fl_exact g 0UL

/// ---------------------------------------------------------------------------
/// Exactness in terms of `blue_blocks`
/// ---------------------------------------------------------------------------

/// Membership introduction for `seq_filter` (the companion of `seq_filter_mem`).
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
private let rec seq_filter_mem_intro (#a: eqtype) (f: a -> GTot bool) (s: Seq.seq a) (x: a)
  : Lemma (requires Seq.mem x s /\ f x)
          (ensures Seq.mem x (seq_filter f s))
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else begin
      let hd = Seq.head s in
      let tl = Seq.tail s in
      Seq.lemma_mem_inversion s;
      if f hd then begin
        mem_cons_lemma x hd (seq_filter f tl);
        if x <> hd then seq_filter_mem_intro f tl x
      end else seq_filter_mem_intro f tl x
    end
#pop-options

/// **The free list is exactly the blue blocks that can hold a link.**
///
/// This is the reviewer's property in the repository's own vocabulary, with
/// the correction the fragment forces. It used to say `blue_blocks`, the blue
/// objects of the heap, full stop. That is false once a wosize-0 block can be
/// blue: such a block is free space, it is in `blue_blocks`, and it cannot be
/// on the chain, because a cell needs a field to hold the link. The set the
/// free list coincides with is the blue blocks that have one.
let cell_blocks (g: heap) : GTot (Seq.seq obj_addr) =
  seq_filter (fun h -> is_blue h g && U64.v (wosize_of_object h g) >= 1)
             (objects zero_addr g)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let fl_exact_cell_blocks (g: heap) (fp: U64.t)
  : Lemma (requires fl_exact g fp)
          (ensures forall (obj: obj_addr).
                     Seq.mem obj (cell_blocks g) <==> reachable_on_fl g fp obj)
  = let f = (fun (h: obj_addr) -> is_blue h g && U64.v (wosize_of_object h g) >= 1) in
    introduce forall (obj: obj_addr). Seq.mem obj (cell_blocks g) <==> reachable_on_fl g fp obj
    with begin
      introduce Seq.mem obj (cell_blocks g) ==> reachable_on_fl g fp obj
      with begin
        seq_filter_mem f (objects zero_addr g) obj;
        fl_complete_elim g fp obj
      end;
      introduce reachable_on_fl g fp obj ==> Seq.mem obj (cell_blocks g)
      with seq_filter_mem_intro f (objects zero_addr g) obj
    end
#pop-options
