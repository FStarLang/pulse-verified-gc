/// The real side of the id-level accounting: the invariant `acc_inv` that
/// ties a real state, its history and its map from blocks to objects to an
/// accounting state (`GC.Gen.Run.IdAccounting.acc`), and the frame lemmas
/// the per-step proofs (`GC.Gen.Run.Hoisted.Steps`) share.
module GC.Gen.Run.Hoisted.Frame

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.MinorHeap
open GC.Gen.Run.Step
open GC.Gen.Run.History
open GC.Gen.Run.Invariant
open GC.Model.Represents
open GC.Gen.Run.Simulation
open GC.Gen.Run.IdAccounting
open GC.Gen.Run.Hoisted.Base

module U64 = FStar.UInt64
module I = GC.Model.Ideal

/// ---------------------------------------------------------------------------
/// The invariant
/// ---------------------------------------------------------------------------

/// The kept major blocks hold exactly the accounting's `kept`.
let kept_rep (h: cycle_history) (ids: block_id_map) (a: acc) : prop =
  forall (id: I.obj_id). (exists (x: obj_addr). ids (Major x) == Some id /\ kept h x) <==> a.kept id

/// The remembered set holds exactly the accounting's remembered slots, each
/// in a kept block; and there are none with an empty nursery.
let rt_rep (r: real_state) (ids: block_id_map) (a: acc) : prop =
  (forall (j: nat). j < Seq.length r.ref_table ==>
     (exists (x: obj_addr) (i: nat) (xid: I.obj_id).
        ids (Major x) == Some xid /\ a.rt xid i /\ Seq.index r.ref_table j == major_slot x i)) /\
  (forall (xid: I.obj_id) (i: nat). a.rt xid i ==>
     a.kept xid /\
     (exists (x: obj_addr) (j: nat). ids (Major x) == Some xid /\ j < Seq.length r.ref_table /\
        Seq.index r.ref_table j == major_slot x i)) /\
  ((exists (xid: I.obj_id) (i: nat). a.rt xid i) ==> (exists (id: I.obj_id). a.nurs id))

/// **The accounting invariant.**
let acc_inv (r: real_state) (h: cycle_history) (ids: block_id_map) (a: acc) : prop =
  nurs_rep ids a /\ kept_rep h ids a /\ rt_rep r ids a

/// The invariant only reads `nurs`, `kept` and `rt`, pointwise.
let same_sets (a a': acc) : prop =
  (forall (id: I.obj_id). a.nurs id <==> a'.nurs id) /\
  (forall (id: I.obj_id). a.kept id <==> a'.kept id) /\
  (forall (id: I.obj_id) (i: nat). a.rt id i <==> a'.rt id i)

let acc_inv_ext (r: real_state) (h: cycle_history) (ids: block_id_map) (a a': acc)
  : Lemma (requires acc_inv r h ids a /\ same_sets a a') (ensures acc_inv r h ids a')
  = ()

/// The history matters only through `kept`.
let kept_rep_ext (h h': cycle_history) (ids: block_id_map) (a: acc)
  : Lemma (requires kept_rep h ids a /\ (forall (x: obj_addr). kept h x <==> kept h' x))
          (ensures kept_rep h' ids a)
  = ()

/// ---------------------------------------------------------------------------
/// Kept blocks stay
/// ---------------------------------------------------------------------------

/// A kept block is an allocated block (B2, B3).
let kept_allocated (r: real_state) (h: cycle_history) (x: obj_addr)
  : Lemma (requires run_invariant r h /\ kept h x) (ensures is_allocated r.memory (Major x))
  = ()

/// The block of an accounted remembered slot is the kept block of its object.
let rt_block_kept (h: cycle_history) (ids: block_id_map) (a: acc) (m: real_memory)
                  (x: obj_addr) (xid: I.obj_id)
  : Lemma (requires kept_rep h ids a /\ ids_injective_on_allocated m ids /\ a.kept xid /\ ids (Major x) == Some xid)
          (ensures kept h x)
  = eliminate exists (x2: obj_addr). ids (Major x2) == Some xid /\ kept h x2
    with assert (Major x2 == Major x)

/// **The frame for `nurs` and `kept`**: from `r` to `r'` the history and the
/// nursery's allocated blocks are the same, and the map is restricted to
/// what is allocated in `r'`.
let nurs_kept_frame (r r': real_state) (h: cycle_history) (ids: block_id_map) (a: acc)
  : Lemma (requires nurs_rep ids a /\ kept_rep h ids a /\ ids_injective_on_allocated r.memory ids /\
                    (forall (x: obj_addr). kept h x ==> is_allocated r'.memory (Major x)) /\
                    (forall (o: U64.t). is_allocated r'.memory (Nursery o) <==> is_allocated r.memory (Nursery o)))
          (ensures nurs_rep (restrict r'.memory ids) a /\ kept_rep h (restrict r'.memory ids) a /\
                   (forall (x: obj_addr). kept h x ==> restrict r'.memory ids (Major x) == ids (Major x)) /\
                   (forall (o: U64.t). restrict r'.memory ids (Nursery o) == ids (Nursery o)))
  = let ids' = restrict r'.memory ids in
    let nk (o: U64.t) : Lemma (ids' (Nursery o) == ids (Nursery o)) = () in
    FStar.Classical.forall_intro nk;
    let kk (x: obj_addr) : Lemma (kept h x ==> ids' (Major x) == ids (Major x)) = () in
    FStar.Classical.forall_intro kk;
    introduce forall (id: I.obj_id). (exists (x: obj_addr). ids' (Major x) == Some id /\ kept h x) <==> a.kept id
    with begin
      introduce (exists (x: obj_addr). ids' (Major x) == Some id /\ kept h x) ==> a.kept id
      with eliminate exists (x: obj_addr). ids' (Major x) == Some id /\ kept h x
              with kk x;
      introduce a.kept id ==> (exists (x: obj_addr). ids' (Major x) == Some id /\ kept h x)
      with eliminate exists (x: obj_addr). ids (Major x) == Some id /\ kept h x
              with kk x
    end

/// **The frame for the remembered set**: the same table and slots, and every
/// kept block keeps its id.
let rt_frame (r r': real_state) (h: cycle_history) (ids ids': block_id_map) (a: acc)
  : Lemma (requires rt_rep r ids a /\ kept_rep h ids a /\ ids_injective_on_allocated r.memory ids /\
                    r'.ref_table == r.ref_table /\
                    (forall (x: obj_addr). kept h x ==> ids' (Major x) == ids (Major x)))
          (ensures rt_rep r' ids' a)
  = let fix (x: obj_addr) (xid: I.obj_id) (i: nat)
      : Lemma (requires ids (Major x) == Some xid /\ a.rt xid i) (ensures ids' (Major x) == Some xid)
      = rt_block_kept h ids a r.memory x xid in
    introduce forall (j: nat). j < Seq.length r'.ref_table ==>
      (exists (x: obj_addr) (i: nat) (xid: I.obj_id).
         ids' (Major x) == Some xid /\ a.rt xid i /\ Seq.index r'.ref_table j == major_slot x i)
    with introduce _ ==> _
    with eliminate exists (x: obj_addr) (i: nat) (xid: I.obj_id).
           ids (Major x) == Some xid /\ a.rt xid i /\ Seq.index r.ref_table j == major_slot x i
         with fix x xid i;
    introduce forall (xid: I.obj_id) (i: nat). a.rt xid i ==>
      a.kept xid /\
      (exists (x: obj_addr) (j: nat). ids' (Major x) == Some xid /\ j < Seq.length r'.ref_table /\
         Seq.index r'.ref_table j == major_slot x i)
    with introduce _ ==> _
    with eliminate exists (x: obj_addr) (j: nat). ids (Major x) == Some xid /\ j < Seq.length r.ref_table /\
           Seq.index r.ref_table j == major_slot x i
         with fix x xid i
         ;
    assert ((exists (xid: I.obj_id) (i: nat). a.rt xid i) ==> (exists (id: I.obj_id). a.nurs id))
