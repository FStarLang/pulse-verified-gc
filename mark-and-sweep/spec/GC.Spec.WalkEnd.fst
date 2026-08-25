module GC.Spec.WalkEnd

/// The heap walk as a scalar.
///
/// `GC.Spec.SweepInv.heap_objects_dense` says that the object walk tiles the
/// heap: it stops only when there is no room left for another header, never
/// because a block claims more space than the heap has.  Stated as a quantifier
/// over walk positions it is awkward to *transport* across a phase that changes
/// block sizes, such as coalescing.
///
/// `walk_end g start` records the single address at which the walk starting at
/// `start` comes to a stop.  Density then becomes one scalar equation --
/// `walk_end g zero_addr + 8 >= heap_size` -- and a phase preserves density
/// exactly when it preserves that address.

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header

module U64 = FStar.UInt64
module SweepInv = GC.Spec.SweepInv

#set-options "--fuel 0 --ifuel 0 --z3rlimit 40"

/// ---------------------------------------------------------------------------
/// Definition
/// ---------------------------------------------------------------------------

#push-options "--fuel 1 --ifuel 1"
let rec walk_end (g: heap) (start: hp_addr)
  : GTot nat (decreases (heap_size - U64.v start))
  = if U64.v start + 8 >= heap_size then U64.v start
    else
      let wz = getWosize (read_word g start) in
      let next = U64.v start + (U64.v wz + 1) * 8 in
      if next > heap_size || next >= pow2 64 then U64.v start
      else if next >= heap_size then next
      else begin
        aligned_plus_mul8 (U64.v start) (U64.v wz + 1);
        walk_end g (mk_hp_addr next)
      end
#pop-options

/// One step of the walk, phrased against `objects` so that callers never have
/// to unfold `walk_end` themselves.
#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
let walk_end_step (g: heap) (start: hp_addr)
  : Lemma
    (requires Seq.length (objects start g) > 0)
    (ensures (
      let wz = getWosize (read_word g start) in
      let next = U64.v start + (U64.v wz + 1) * 8 in
      U64.v start + 8 < heap_size /\ next <= heap_size /\ next % 8 == 0 /\
      (next >= heap_size ==>
       walk_end g start == heap_size /\
       objects start g == Seq.cons (f_address start) Seq.empty) /\
      (next < heap_size ==>
       Seq.length (objects start g) == 1 + Seq.length (objects (mk_hp_addr next) g) /\
       Seq.head (objects start g) == f_address start /\
       Seq.tail (objects start g) == objects (mk_hp_addr next) g /\
       walk_end g start == walk_end g (mk_hp_addr next))))
  = let wz = getWosize (read_word g start) in
    let next = U64.v start + (U64.v wz + 1) * 8 in
    aligned_plus_mul8 (U64.v start) (U64.v wz + 1);
    if next < heap_size then
      Seq.lemma_tl (f_address start) (objects (mk_hp_addr next) g)
#pop-options

/// The head of a non-empty walk is the object at the walk position.
#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let walk_head (g: heap) (start: hp_addr)
  : Lemma
    (requires Seq.length (objects start g) > 0)
    (ensures Seq.mem (f_address start) (objects start g) /\
             Seq.head (objects start g) == f_address start)
  = ()
#pop-options

/// ---------------------------------------------------------------------------
/// `walk_end` reaches the end of the heap  <==>  the walk is dense
/// ---------------------------------------------------------------------------

/// A walk with no room left for a header stops where it starts.
#push-options "--fuel 1 --ifuel 1"
let walk_end_at_tail (g: heap) (q: hp_addr)
  : Lemma (requires U64.v q + 8 >= heap_size)
          (ensures walk_end g q == U64.v q)
  = ()
#pop-options

/// A walk that enumerates nothing stops where it starts.
#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let walk_end_empty (g: heap) (q: hp_addr)
  : Lemma (requires Seq.length (objects q g) == 0)
          (ensures walk_end g q == U64.v q)
  = ()
#pop-options

/// A walk whose end lies at the end of the heap is non-empty: had the block at
/// `q` overrun the heap, the walk would have stopped at `q` itself.
#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
let walk_nonempty_of_walk_end (g: heap) (q: hp_addr)
  : Lemma
    (requires U64.v q + 8 < heap_size /\ walk_end g q + 8 >= heap_size)
    (ensures Seq.length (objects q g) > 0)
  = ()
#pop-options

/// Density at a single walk position, given that the walk containing it runs
/// all the way to the end of the heap.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
let rec dense_at (g: heap) (p: hp_addr) (start: hp_addr)
  : Lemma
    (requires U64.v start + 8 < heap_size /\
              walk_end g p + 8 >= heap_size /\
              Seq.mem (f_address start) (objects p g))
    (ensures (
      let wz = getWosize (read_word g start) in
      let next = U64.v start + ((U64.v wz + 1) * 8) in
      next + 8 < heap_size ==>
      Seq.length (objects (U64.uint_to_t next) g) > 0 /\
      Seq.mem (f_address (U64.uint_to_t next)) (objects p g)))
    (decreases (heap_size - U64.v p))
  = walk_end_step g p;
    walk_head g p;
    f_address_spec p;
    f_address_spec start;
    let wzp = getWosize (read_word g p) in
    let np = U64.v p + (U64.v wzp + 1) * 8 in
    let wz = getWosize (read_word g start) in
    let next = U64.v start + ((U64.v wz + 1) * 8) in
    if next + 8 >= heap_size then ()
    else begin
      if np >= heap_size then begin
        // The walk from `p` holds exactly one object, so `start == p`, and then
        // `next == np >= heap_size` contradicts `next + 8 < heap_size`.
        mem_cons_lemma (f_address start) (f_address p) Seq.empty;
        assert (U64.v start == U64.v p);
        assert False
      end
      else begin
        let npa : hp_addr = mk_hp_addr np in
        if U64.v start = U64.v p then begin
          assert (next == np);
          walk_nonempty_of_walk_end g npa;
          walk_head g npa;
          mem_cons_lemma (f_address npa) (f_address p) (objects npa g)
        end
        else begin
          mem_cons_lemma (f_address start) (f_address p) (objects npa g);
          assert (Seq.mem (f_address start) (objects npa g));
          dense_at g npa start;
          mem_cons_lemma (f_address (U64.uint_to_t next)) (f_address p) (objects npa g)
        end
      end;
      assert (Seq.length (objects (U64.uint_to_t next) g) > 0);
      assert (Seq.mem (f_address (U64.uint_to_t next)) (objects p g))
    end
#pop-options

/// A walk that reaches the end of the heap is dense.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"
let dense_from_walk_end (g: heap)
  : Lemma
    (requires Seq.length (objects zero_addr g) > 0 /\
              walk_end g zero_addr + 8 >= heap_size)
    (ensures SweepInv.heap_objects_dense g)
  = let aux (start: hp_addr)
      : Lemma
        (ensures
          U64.v start + 8 < heap_size ==>
          Seq.mem (f_address start) (objects zero_addr g) ==>
          Seq.length (objects start g) > 0 ==>
          (let wz = getWosize (read_word g start) in
           let next = U64.v start + ((U64.v wz + 1) * 8) in
           next + 8 < heap_size ==>
           Seq.length (objects (U64.uint_to_t next) g) > 0 /\
           Seq.mem (f_address (U64.uint_to_t next)) (objects zero_addr g)))
      = if U64.v start + 8 < heap_size &&
           Seq.mem (f_address start) (objects zero_addr g)
        then dense_at g zero_addr start
    in
    FStar.Classical.forall_intro aux;
    SweepInv.heap_objects_dense_intro g
#pop-options

/// Conversely, a dense walk reaches the end of the heap.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 80"
let rec walk_end_of_dense (g: heap) (p: hp_addr)
  : Lemma
    (requires U64.v p + 8 < heap_size /\
              SweepInv.heap_objects_dense g /\
              Seq.mem (f_address p) (objects zero_addr g) /\
              Seq.length (objects p g) > 0)
    (ensures walk_end g p + 8 >= heap_size)
    (decreases (heap_size - U64.v p))
  = walk_end_step g p;
    let wz = getWosize (read_word g p) in
    let np = U64.v p + (U64.v wz + 1) * 8 in
    if np >= heap_size then ()
    else begin
      let npa : hp_addr = mk_hp_addr np in
      if np + 8 >= heap_size then walk_end_at_tail g npa
      else begin
        SweepInv.objects_dense_step p g;
        SweepInv.objects_dense_obj_in p g;
        f_address_spec npa;
        SweepInv.obj_in_objects_elim (f_address npa) g;
        walk_end_of_dense g npa
      end
    end
#pop-options

/// Top-level form: density is exactly "the walk from `zero_addr` reaches the
/// end of the heap".
let walk_end_of_dense_top (g: heap)
  : Lemma
    (requires SweepInv.heap_objects_dense g /\
              Seq.length (objects zero_addr g) > 0)
    (ensures walk_end g zero_addr + 8 >= heap_size)
  = walk_head g zero_addr;
    walk_end_of_dense g zero_addr
