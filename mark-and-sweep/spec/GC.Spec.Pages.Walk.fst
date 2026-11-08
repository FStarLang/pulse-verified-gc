/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Walk - the heap walk over a stretch of the heap
/// ---------------------------------------------------------------------------
///
/// `steps_to g a b`: the walk that starts at the header at `a` lands exactly
/// on `b`, every block on the way lying inside `[a, b)`.  It is the local
/// form of the tiling invariant: a page, a slot or a large run is tiled when
/// the walk from its start steps to its end.
///
/// The bridge lemmas tie it to the global walk `objects zero_addr g` and to
/// its end `GC.Spec.WalkEnd.walk_end`: a heap whose pages are each tiled is
/// tiled as a whole, and every position the walk steps to is an object.

module GC.Spec.Pages.Walk

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields

module U64 = FStar.UInt64
module Seq = FStar.Seq
module WE = GC.Spec.WalkEnd

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

/// The size in bytes of the block whose header is at `a`.
let block_bytes (g: heap) (a: hp_addr) : nat =
  (U64.v (getWosize (read_word g a)) + 1) * 8

#push-options "--fuel 1 --ifuel 1"
let rec steps_to (g: heap) (a b: nat)
  : GTot bool (decreases (if a <= b then b - a else 0))
  = if a = b then true
    else if a > b || b > heap_size || a % 8 <> 0 then false
    else begin
      let nx = a + block_bytes g (mk_hp_addr a) in
      nx <= b && steps_to g nx b
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Building walks
/// ---------------------------------------------------------------------------

#push-options "--fuel 1 --ifuel 1"
let steps_to_refl (g: heap) (a: nat)
  : Lemma (steps_to g a a)
  = ()

let rec steps_to_le (g: heap) (a b: nat)
  : Lemma (requires steps_to g a b)
          (ensures a <= b /\ (a < b ==> b <= heap_size /\ a % 8 == 0))
          (decreases (if a <= b then b - a else 0))
  = if a = b then ()
    else steps_to_le g (a + block_bytes g (mk_hp_addr a)) b

/// One block.
let steps_to_one (g: heap) (a: hp_addr) (b: nat)
  : Lemma (requires b == U64.v a + block_bytes g a /\ b <= heap_size)
          (ensures steps_to g (U64.v a) b)
  = assert (mk_hp_addr (U64.v a) == a);
    steps_to_refl g b;
    assert (U64.v a < b);
    assert_norm (steps_to g (U64.v a) b ==
      (if U64.v a = b then true
       else if U64.v a > b || b > heap_size || U64.v a % 8 <> 0 then false
       else (let nx = U64.v a + block_bytes g (mk_hp_addr (U64.v a)) in
             nx <= b && steps_to g nx b)))

let rec steps_to_trans (g: heap) (a b c: nat)
  : Lemma (requires steps_to g a b /\ steps_to g b c)
          (ensures steps_to g a c)
          (decreases (if a <= b then b - a else 0))
  = steps_to_le g a b;
    steps_to_le g b c;
    if a = b then ()
    else begin
      let nx = a + block_bytes g (mk_hp_addr a) in
      steps_to_trans g nx b c
    end

/// A walk that moves takes its first block, then walks on from there.
let steps_to_next (g: heap) (a: hp_addr) (b: nat)
  : Lemma (requires steps_to g (U64.v a) b /\ U64.v a < b)
          (ensures U64.v a + block_bytes g a <= b /\
                   steps_to g (U64.v a + block_bytes g a) b)
  = assert (mk_hp_addr (U64.v a) == a)

/// The walk reads only the headers it lands on, all inside `[a, b)`.
let rec steps_to_frame (g g': heap) (a b: nat)
  : Lemma (requires forall (x: hp_addr). a <= U64.v x /\ U64.v x < b ==>
                      read_word g' x == read_word g x)
          (ensures steps_to g' a b == steps_to g a b)
          (decreases (if a <= b then b - a else 0))
  = if a = b || a > b || b > heap_size || a % 8 <> 0 then ()
    else begin
      let nx = a + block_bytes g (mk_hp_addr a) in
      if nx <= b then steps_to_frame g g' nx b
    end
#pop-options

/// ---------------------------------------------------------------------------
/// The bridge to the global walk
/// ---------------------------------------------------------------------------

/// A position the walk from `s` steps to, with a whole block above it that
/// leaves room for its header, is an object of the walk from `s`.
#push-options "--fuel 2 --ifuel 1"
let rec steps_to_objects (g: heap) (s: hp_addr) (a: hp_addr) (b: nat)
  : Lemma (requires steps_to g (U64.v s) (U64.v a) /\
                    b == U64.v a + block_bytes g a /\ b <= heap_size /\
                    U64.v a + 8 < heap_size)
          (ensures Seq.mem (f_address a) (objects s g))
          (decreases (U64.v a - U64.v s))
  = steps_to_le g (U64.v s) (U64.v a);
    f_address_spec a;
    if U64.v s = U64.v a then begin
      assert (s == a);
      WE.walk_end_step g s
    end else begin
      let nx = U64.v s + block_bytes g s in
      assert (mk_hp_addr (U64.v s) == s);
      steps_to_le g nx (U64.v a);
      aligned_plus_mul8 (U64.v s) (U64.v (getWosize (read_word g s)) + 1);
      let nxa = mk_hp_addr nx in
      steps_to_objects g nxa a b;
      objects_cons_step_to s g nxa;
      mem_cons_lemma (f_address a) (f_address s) (objects nxa g)
    end
#pop-options

/// A walk that steps to the end of the heap, up to a last word too small
/// for a header, gives density as `GC.Spec.WalkEnd` states it.
#push-options "--fuel 1 --ifuel 1"
let rec steps_to_walk_end (g: heap) (s: hp_addr) (e: nat)
  : Lemma (requires steps_to g (U64.v s) e /\ e <= heap_size /\ e + 8 >= heap_size)
          (ensures WE.walk_end g s + 8 >= heap_size)
          (decreases (e - U64.v s))
  = steps_to_le g (U64.v s) e;
    if U64.v s + 8 >= heap_size then ()
    else if U64.v s = e then ()
    else begin
      assert (mk_hp_addr (U64.v s) == s);
      let wz = getWosize (read_word g s) in
      let nx = U64.v s + (U64.v wz + 1) * 8 in
      if nx >= heap_size then ()
      else begin
        aligned_plus_mul8 (U64.v s) (U64.v wz + 1);
        steps_to_walk_end g (mk_hp_addr nx) e
      end
    end
#pop-options

/// Every object of the walk from `s` sits at a position the walk steps to.
#push-options "--fuel 2 --ifuel 1"
let rec objects_steps_to (g: heap) (s: hp_addr) (x: obj_addr)
  : Lemma (requires Seq.mem x (objects s g))
          (ensures steps_to g (U64.v s) (U64.v (hd_address x)) /\
                   U64.v (hd_address x) + 8 < heap_size)
          (decreases (heap_size - U64.v s))
  = hd_address_spec x;
    WE.walk_end_step g s;
    WE.walk_head g s;
    f_address_spec s;
    if x = f_address s then ()
    else begin
      let wz = getWosize (read_word g s) in
      let nx = U64.v s + (U64.v wz + 1) * 8 in
      assert (mk_hp_addr (U64.v s) == s);
      if nx >= heap_size then
        mem_cons_lemma x (f_address s) Seq.empty
      else begin
        let nxa = mk_hp_addr nx in
        mem_cons_lemma x (f_address s) (objects nxa g);
        objects_steps_to g nxa x;
        steps_to_one g s nx;
        steps_to_trans g (U64.v s) nx (U64.v (hd_address x))
      end
    end
#pop-options
