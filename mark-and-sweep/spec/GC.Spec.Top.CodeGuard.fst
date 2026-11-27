/// ---------------------------------------------------------------------------
/// GC.Spec.Top.CodeGuard - the nursery's run-time guards hold where followed
/// ---------------------------------------------------------------------------
///
/// Design doc §18, step 2.  The Pulse promotion takes an address that passes
/// its run-time guards for a nursery object (`Promote.Guard`), at the roots
/// and at the scanned fields.  On a nursery the model represents, a young
/// pointer the model resolves passes them only at a block's start: the
/// model's resolution is `resolve_minor`'s (`Young.young_resolve`), and an
/// address it resolves past a block start is an infix one, which the guards
/// refuse.  So the guards hold at every scanned field whose young pointers
/// resolve (`fields_gd_of`) and at every root word the minor collection
/// forwards (`roots_gd_of`).

module GC.Spec.Top.CodeGuard

open FStar.Seq
open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Spec.Top.Word
module M = GC.Spec.Top.Heap
module U64 = FStar.UInt64
module Y = GC.Spec.Top.Young
module PC = GC.Spec.Top.PromoteCopy
module Q = GC.Spec.Top.PagesQueue
module LV = GC.Spec.Top.PagesLive
module Gd = GC.Spec.Pages.Promote.Guard

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// **A young pointer the model resolves** passes the guards only at an
/// object.
#push-options "--z3rlimit 40"
let gd_resolve (m: M.mheap) (ms: minor_state) (a o: nat)
  : Lemma (requires Y.yrepr m ms /\ a + 1 < ywords /\ M.resolve m a == Some o)
          (ensures (Y.msz (); Gd.gd_ok ms (U64.uint_to_t (8 * a + 8))))
  = Y.msz ();
    let v = U64.uint_to_t (8 * a + 8) in
    Y.young_resolve m ms a o;
    if is_infix_in_minor ms v then ()
    else begin
      resolve_minor_non_infix ms v;
      assert (U64.v v == 8 * o + 8);
      GC.Spec.Top.ToyMark.resolve_resolves m a o;
      PC.young_obj m ms o;
      assert (PC.yobj o == v)
    end
#pop-options

/// A word that is not a young pointer fails the guards.
let gd_not_young (ms: minor_state) (v: U64.t)
  : Lemma (requires not (is_young_w v)) (ensures Gd.gd_ok ms v)
  = ()

/// A young word is a young pointer the model reads.
let young_word_of (v: U64.t)
  : Lemma (requires is_young_w v)
          (ensures (let a = (U64.v v - 8) / 8 in
                    U64.v v == 8 * a + 8 /\ a + 1 < ywords /\ v == U64.uint_to_t (8 * a + 8) /\
                    absv v == M.VPtr (M.Young a)))
  = Y.msz ();
    base_facts ();
    GC.Gen.Base.zero_addr_above_minor ();
    let a = (U64.v v - 8) / 8 in
    FStar.Math.Lemmas.lemma_div_exact (U64.v v - 8) 8;
    U64.v_inj v (U64.uint_to_t (8 * a + 8))

/// One scanned field.
#push-options "--z3rlimit 40"
let field_gd (y: M.mheap) (ms: minor_state) (x: U64.t) (i: nat)
  : Lemma (requires Y.yrepr y ms /\
                    (forall (o j b: nat). M.ptr_field y o j /\ M.field y o j == M.VPtr (M.Young b) ==>
                                         Some? (M.resolve y b)) /\
                    Seq.mem x (minor_objects ms) /\ i < minor_scan_wosize ms x)
          (ensures Gd.gd_ok ms (to_minor_offset (minor_read_field ms x i)))
  = Q.obj_young y ms x;
    let o = Q.yof x in
    PC.young_obj y ms o;
    minor_scan_wosize_cases ms x;
    let f = minor_read_field ms x i in
    LV.tmo_id f;
    PC.young_field y ms o i;
    if is_young_w f then begin
      young_word_of f;
      let a = (U64.v f - 8) / 8 in
      assert (M.ptr_field y o i);
      assert (M.field y o i == M.VPtr (M.Young a));
      let t = Some?.v (M.resolve y a) in
      gd_resolve y ms a t
    end
    else gd_not_young ms f
#pop-options

/// **The scanned fields pass the guards only at objects.**
let fields_gd_of (y: M.mheap) (ms: minor_state)
  : Lemma (requires Y.yrepr y ms /\
                    (forall (o j b: nat). M.ptr_field y o j /\ M.field y o j == M.VPtr (M.Young b) ==>
                                         Some? (M.resolve y b)))
          (ensures Gd.fields_gd ms)
  = Gd.fields_gd_intro ms (fun x i -> field_gd y ms x i)

/// **So do the roots the minor collection forwards.**
let roots_gd_of (w: M.world) (ms: minor_state)
  : Lemma (requires Y.yrepr w.M.yng ms) (ensures Gd.roots_gd ms (LV.roots_of w))
  = let one (i: nat) : Lemma (i < Seq.length (LV.roots_of w) ==> Gd.gd_ok ms (Seq.index (LV.roots_of w) i))
      = if i < Seq.length (LV.roots_of w) then begin
          let r = Seq.index (LV.roots_of w) i in
          GC.Spec.Top.ByteMark.mem_of_index (LV.roots_of w) i;
          LV.roots_ok w r;
          eliminate exists (a o: nat). 8 * a + 16 <= minor_heap_size /\ U64.v r == 8 * a + 8 /\
                                      M.resolve w.M.yng a == Some o /\ M.minor_live w o
          with begin
            LV.a1_lt a;
            Y.msz ();
            U64.v_inj r (U64.uint_to_t (8 * a + 8));
            gd_resolve w.M.yng ms a o
          end
        end in
    FStar.Classical.forall_intro one
