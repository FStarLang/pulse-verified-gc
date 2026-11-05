/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPhase.Mutator - the program's field writes and loads while marking
/// ---------------------------------------------------------------------------
///
/// Between mark slices the program runs.  This module is about its field
/// writes into the major heap, and the loads by which it obtains pointers, at
/// the marking invariant `GC.Spec.MarkPhase.marking_inv g held` (`held`: what
/// is pointed at from outside the major heap -- the program's roots and the
/// nursery's fields, chosen by the generational layer).
///
///   * **What a write changes** (`write_*`): a write into a body word `a` of a
///     non-free object `x` that is not a closure keeps the walk and every
///     header; only `x`'s edges change.  Every other block's edges are kept
///     (`write_edges_other`).  An edge of `x` afterwards is an old one or goes
///     to the new value's target (`write_edges_new`); an old edge of `x` is
///     kept or went to the old value's target (`write_edges_old`).  These need
///     the targets of pointers in non-free blocks to keep their resolution,
///     which holds because their headers are walk positions or infix headers
///     inside closures, never a body word of `x` (`target_header_away`).
///   * **The write** (`marking_write`): `marking_inv` survives the write when
///     the old value's target is not white (no edge into a white object is
///     cut unseen) and the new value's target is not white, held, or one the
///     marker will reach (a black `x` may then point at it).  Writing an
///     immediate (`marking_write_immediate`) is the instance with no target.
///   * **The deletion barrier** (`marking_write_barrier`): darken the old
///     value first (`darken`, 4.14's `caml_darken`), then write: the cut edge
///     ends at a grey object, so every path the marker would follow restarts
///     there.
///   * **Loads** (`marking_load`): a field of an object the program holds,
///     loaded into a register, is one the marker will reach if white -- so
///     the program may hold it too.  This is why clause 2 of the invariant
///     stays true of the program's roots between collector events.

module GC.Spec.MarkPhase.Mutator

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.MarkPhase

module U64 = FStar.UInt64
module SPI = GC.Spec.SweepPhase.Intrinsic
module SPM = GC.Spec.SweepPhase.Mutator

/// ---------------------------------------------------------------------------
/// What a write changes
/// ---------------------------------------------------------------------------

/// The value `w` points (resolved) at `t`.
let value_target (g: heap) (w: U64.t) (t: obj_addr) : prop =
  is_pointer w /\ resolve_object (w <: obj_addr) g == t

/// A storable value's header -- a walk position, or an infix header inside a
/// closure -- is not a body word of a non-free object that is not a closure.
val target_header_away (g: heap) (x: obj_addr) (a: hp_addr) (w: U64.t)
  : Lemma (requires well_formed_heap g /\ in_use free_stw g x /\ ~(is_closure x g) /\
                    SPM.in_body g x a /\ is_pointer w /\ SPI.storable free_stw g w)
          (ensures hd_address (w <: obj_addr) <> a /\
                   (forall (v: U64.t). resolve_object (w <: obj_addr) (write_word g a v) ==
                                  resolve_object (w <: obj_addr) g))

/// A write into the body of a non-free object keeps the walk and every header.
val write_heads (g: heap) (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) /\ SPM.in_body g x a)
          (ensures SPI.same_heads g (write_word g a v) /\
                   objects zero_addr (write_word g a v) == objects zero_addr g /\
                   (forall (y: obj_addr). Seq.mem y (objects zero_addr g) ==>
                      read_word (write_word g a v) (hd_address y) == read_word g (hd_address y) /\
                      (is_black y (write_word g a v) <==> is_black y g) /\
                      (is_white y (write_word g a v) <==> is_white y g) /\
                      (is_gray y (write_word g a v) <==> is_gray y g) /\
                      (is_blue y (write_word g a v) <==> is_blue y g) /\
                      is_no_scan y (write_word g a v) == is_no_scan y g /\
                      is_closure y (write_word g a v) == is_closure y g))

/// The write keeps well-formedness (`SPM.program_write`: the new value is
/// storable if `x` is scannable).
val write_wf (g: heap) (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires well_formed_heap g /\ SPM.program_write free_stw g x a v)
          (ensures well_formed_heap (write_word g a v))

/// Every other non-free block keeps its edges.
val write_edges_other (g: heap) (x: obj_addr) (a: hp_addr) (v: U64.t) (u t: obj_addr)
  : Lemma (requires well_formed_heap g /\ in_use free_stw g x /\ ~(is_closure x g) /\
                    SPM.in_body g x a /\ in_use free_stw g u /\ u <> x)
          (ensures field_edge (write_word g a v) u t <==> field_edge g u t)

/// An edge of `x` after the write is an old one or goes to the new value's
/// target.
val write_edges_new (g: heap) (x: obj_addr) (a: hp_addr) (v: U64.t) (t: obj_addr)
  : Lemma (requires well_formed_heap g /\ SPM.program_write free_stw g x a v /\
                    field_edge (write_word g a v) x t)
          (ensures field_edge g x t \/ value_target g v t)

/// An edge of `x` before the write is kept, or went to the old value's target.
val write_edges_old (g: heap) (x: obj_addr) (a: hp_addr) (v: U64.t) (t: obj_addr)
  : Lemma (requires well_formed_heap g /\ SPM.program_write free_stw g x a v /\ field_edge g x t)
          (ensures field_edge (write_word g a v) x t \/ value_target g (read_word g a) t)

/// ---------------------------------------------------------------------------
/// The write
/// ---------------------------------------------------------------------------

/// The old value's target, if any, is not white.
let target_not_white (g: heap) (w: U64.t) : prop =
  is_pointer w ==> ~(is_white (resolve_object (w <: obj_addr) g) g)

/// The new value's target, if any, may be pointed at by a black object: it
/// is not white, or it is held, or the marker will reach it.
let target_ok (g: heap) (held: obj_addr -> prop) (w: U64.t) : prop =
  is_pointer w ==>
  (let t = resolve_object (w <: obj_addr) g in
   ~(is_white t g) \/ held t \/ marker_will_reach g t)

/// **A write keeps the marking invariant** when the old target is not white
/// and the new one is fine for a black object to point at (when `x` is
/// scannable: a no-scan block has no edges).  `held` need not change: the
/// program may still hold what it stored.
val marking_write (g: heap) (held: obj_addr -> prop) (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires marking_inv g held /\ SPM.program_write free_stw g x a v /\
                    (~(is_no_scan x g) ==> target_not_white g (read_word g a) /\ target_ok g held v))
          (ensures marking_inv (write_word g a v) held)

/// Writing an immediate (not a pointer) where the old value was not a white
/// object's pointer.
val marking_write_immediate (g: heap) (held: obj_addr -> prop) (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires marking_inv g held /\ in_use free_stw g x /\ ~(is_closure x g) /\ SPM.in_body g x a /\
                    ~(is_pointer v) /\ target_not_white g (read_word g a))
          (ensures marking_inv (write_word g a v) held)

/// ---------------------------------------------------------------------------
/// The deletion barrier
/// ---------------------------------------------------------------------------

/// 4.14's `caml_darken`: grey the object a value points at, if it is a white
/// block.
let darken (g: heap) (w: U64.t) : GTot heap =
  if is_pointer w &&
     Seq.mem (resolve_object (w <: obj_addr) g) (objects zero_addr g) &&
     is_white (resolve_object (w <: obj_addr) g) g
  then makeGray (resolve_object (w <: obj_addr) g) g
  else g

/// Darkening keeps the invariant.
val darken_inv (g: heap) (held: obj_addr -> prop) (w: U64.t)
  : Lemma (requires marking_inv g held)
          (ensures marking_inv (darken g w) held)

/// **The deletion barrier** (4.14's `caml_modify` while marking): darken the
/// old value, then write.  The new value is storable and fine for a black
/// object to point at, as in `marking_write`; the old one is anything.
val marking_write_barrier (g: heap) (held: obj_addr -> prop) (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires marking_inv g held /\ SPM.program_write free_stw g x a v /\
                    (~(is_no_scan x g) ==> target_ok g held v))
          (ensures marking_inv (write_word (darken g (read_word g a)) a v) held)

/// ---------------------------------------------------------------------------
/// Loads
/// ---------------------------------------------------------------------------

/// **A load**: the program holds `s` and reads a field of it pointing at
/// `t`; it may hold `t` too.
val marking_load (g: heap) (held: obj_addr -> prop) (s t: obj_addr)
  : Lemma (requires marking_inv g held /\ held s /\ in_use free_stw g s /\ field_edge g s t)
          (ensures marking_inv g (fun w -> held w \/ w == t))
