(*
   GC.Spec.FreeList — exactness of the free list.

   The allocator walks a chain of blue (free) blocks threaded through field 1 of
   each block.  Two properties tie that chain to the heap colouring:

     soundness    — every cell on the chain is a blue object of the heap
     completeness — every blue object of the heap is a cell on the chain

   Soundness is what keeps the allocator from handing out a live object.
   Completeness is what keeps swept memory from leaking: without it a block may
   be blue (and so never scanned, never marked, never reported live) and yet be
   unreachable from the free-list head, so it can never be handed back out.

   Membership is stated as *reachability* — an existential over the number of
   steps — rather than reachability within a fixed budget.  A budgeted form
   would force every use of the invariant to re-establish a bound on the chain
   length; the existential form needs no counting argument at all.
*)
module GC.Spec.FreeList

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields

module U64 = FStar.UInt64
module Seq = FStar.Seq

/// ---------------------------------------------------------------------------
/// Chain cells
/// ---------------------------------------------------------------------------

/// A usable free-list cell: a valid object address whose link field is in the
/// heap.  Field 1 of an object at address `a` lives at `hd_address a + mword`,
/// which is `a` itself, so the link word occupies `[a, a + mword)`.
let fl_node (a: U64.t) : GTot bool =
  U64.v a >= U64.v mword &&
  U64.v a % U64.v mword = 0 &&
  U64.v a + U64.v mword <= heap_size
/// The link stored in a cell.
let fl_next (g: heap) (a: U64.t) : GTot U64.t =
  if fl_node a then read_word g (a <: hp_addr) else 0UL

/// ---------------------------------------------------------------------------
/// Membership
/// ---------------------------------------------------------------------------

/// `obj` is reachable from `fp` in at most `n` links.
let rec on_fl (g: heap) (fp: U64.t) (obj: U64.t) (n: nat) : GTot bool (decreases n) =
  if n = 0 then false
  else if not (fl_node fp) then false
  else if fp = obj then true
  else on_fl g (fl_next g fp) obj (n - 1)

/// `obj` is on the free list headed by `fp`.
let reachable_on_fl (g: heap) (fp: U64.t) (obj: U64.t) : GTot prop =
  exists (n: nat). on_fl g fp obj n

/// ---------------------------------------------------------------------------
/// Structural lemmas
/// ---------------------------------------------------------------------------

let on_fl_head (g: heap) (fp: U64.t)
  : Lemma (requires fl_node fp)
          (ensures on_fl g fp fp 1)
  = ()

let reachable_head (g: heap) (fp: U64.t)
  : Lemma (requires fl_node fp)
          (ensures reachable_on_fl g fp fp)
  = on_fl_head g fp;
    assert (on_fl g fp fp 1)

let on_fl_cons (g: heap) (fp: U64.t) (obj: U64.t) (n: nat)
  : Lemma (requires fl_node fp /\ on_fl g (fl_next g fp) obj n)
          (ensures on_fl g fp obj (n + 1))
  = ()

let reachable_cons (g: heap) (fp: U64.t) (obj: U64.t)
  : Lemma (requires fl_node fp /\ reachable_on_fl g (fl_next g fp) obj)
          (ensures reachable_on_fl g fp obj)
  = eliminate exists (n: nat). on_fl g (fl_next g fp) obj n
    with (on_fl_cons g fp obj n; assert (on_fl g fp obj (n + 1)))

let on_fl_uncons (g: heap) (fp: U64.t) (obj: U64.t) (n: nat)
  : Lemma (requires on_fl g fp obj n /\ fp <> obj)
          (ensures n >= 1 /\ fl_node fp /\ on_fl g (fl_next g fp) obj (n - 1))
  = ()

let reachable_uncons (g: heap) (fp: U64.t) (obj: U64.t)
  : Lemma (requires reachable_on_fl g fp obj /\ fp <> obj)
          (ensures reachable_on_fl g (fl_next g fp) obj)
  = eliminate exists (n: nat). on_fl g fp obj n
    with (on_fl_uncons g fp obj n; assert (on_fl g (fl_next g fp) obj (n - 1)))

/// Every cell reachable from `fp` is itself a cell.
let rec on_fl_is_node (g: heap) (fp: U64.t) (obj: U64.t) (n: nat)
  : Lemma (requires on_fl g fp obj n)
          (ensures fl_node obj)
          (decreases n)
  = if n = 0 then ()
    else if fp = obj then ()
    else on_fl_is_node g (fl_next g fp) obj (n - 1)

let reachable_is_node (g: heap) (fp: U64.t) (obj: U64.t)
  : Lemma (requires reachable_on_fl g fp obj)
          (ensures fl_node obj)
  = eliminate exists (n: nat). on_fl g fp obj n
    with on_fl_is_node g fp obj n

/// ---------------------------------------------------------------------------
/// The invariant
/// ---------------------------------------------------------------------------

/// Every cell on the chain is a blue object of the heap with room for a link.
///
/// The `wosize >= 1` conjunct used to come from `linkable_heap`, which claimed
/// it of *every* object. That was always too strong, and became false once
/// right-justified allocation could leave a wosize-0 block. The bound belongs
/// here instead: a block with no field cannot hold a link, so it cannot be on
/// a chain at all -- which is exactly what `fl_cell` already says.
let fl_sound (g: heap) (fp: U64.t) : prop =
  forall (obj: U64.t). reachable_on_fl g fp obj ==>
    (fl_node obj /\
     (U64.v obj >= U64.v mword /\ U64.v obj < heap_size /\ U64.v obj % U64.v mword == 0) /\
     Seq.mem (obj <: obj_addr) (objects zero_addr g) /\
     is_blue (obj <: obj_addr) g /\
     U64.v (wosize_of_object (obj <: obj_addr) g) >= 1)

/// Every blue object that *can* be a cell is on the chain.
///
/// The `wosize >= 1` conjunct is not a weakening of intent, it is what "cell"
/// has always meant: `fl_cell` requires it, because a block with no field
/// cannot hold a link. Right-justified allocation can leave such a block, and
/// `sweep_object` can colour one blue, so the older form -- every *blue*
/// object is on the chain -- is simply false on those heaps. It was harmless
/// only because nothing ever established it.
let fl_complete (g: heap) (fp: U64.t) : prop =
  forall (obj: obj_addr). (Seq.mem obj (objects zero_addr g) /\ is_blue obj g
                           /\ U64.v (wosize_of_object obj g) >= 1) ==>
    reachable_on_fl g fp obj

/// The free list is exactly the set of blue objects that can hold a link.
///
/// `fl_sound` is the "only cells" direction and `fl_complete` the "all cells"
/// one; between them the chain is precisely the cellish blue objects. A
/// wosize-0 fragment is blue and in neither, which is the whole point: it is
/// free space that is not on the list, and saying so is what `linkable_heap`
/// refused to allow.
let fl_exact (g: heap) (fp: U64.t) : prop =
  fl_sound g fp /\ fl_complete g fp

/// Instantiate completeness at a single object.
///
/// `fl_complete` carries no explicit SMT pattern, so the solver will not
/// instantiate it at a witness unless `reachable_on_fl g fp y` already appears
/// in the goal -- which is exactly what one is trying to prove. This forces it.
let fl_complete_elim (g: heap) (fp: U64.t) (y: obj_addr)
  : Lemma (requires fl_complete g fp /\ Seq.mem y (objects zero_addr g)
                    /\ is_blue y g /\ U64.v (wosize_of_object y g) >= 1)
          (ensures reachable_on_fl g fp y)
  = ()

/// Soundness is inherited by the tail of the chain.
let fl_sound_tail (g: heap) (fp: U64.t)
  : Lemma (requires fl_sound g fp /\ fl_node fp)
          (ensures fl_sound g (fl_next g fp))
  = introduce forall (obj: U64.t). reachable_on_fl g (fl_next g fp) obj ==>
      (fl_node obj /\
       (U64.v obj >= U64.v mword /\ U64.v obj < heap_size /\ U64.v obj % U64.v mword == 0) /\
       Seq.mem (obj <: obj_addr) (objects zero_addr g) /\
       is_blue (obj <: obj_addr) g /\
       U64.v (wosize_of_object (obj <: obj_addr) g) >= 1)
    with introduce _ ==> _
    with reachable_cons g fp obj

/// ---------------------------------------------------------------------------
/// Write locality
/// ---------------------------------------------------------------------------

/// A word write that does not alias the link word of any reachable cell leaves
/// the chain, and hence membership, untouched.
