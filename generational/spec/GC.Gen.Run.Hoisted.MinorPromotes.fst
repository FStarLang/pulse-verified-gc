/// `GC.Gen.Run.Hoisted.Steps.minor_promotes` from the soundness of the
/// Cheney collection (`cheney_sound`: what it forwards is what it reaches,
/// at fresh blocks, one block per object) and the graph correspondence
/// (`GC.Gen.Run.Hoisted.Minor.minor_graph`).
module GC.Gen.Run.Hoisted.MinorPromotes

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
open GC.Gen.Run.Hoisted.Frame
open GC.Gen.Run.Hoisted.Steps
open GC.Gen.Run.Hoisted.Minor

module U64 = FStar.UInt64
module I = GC.Model.Ideal
module Promote = GC.Gen.Promote
module Reach = GC.Gen.Reachability
module ID = FStar.IndefiniteDescription

/// **What the Cheney collection guarantees** at a minor step from a state of
/// the run invariant: a nursery object is forwarded exactly when it is
/// reachable (through nursery objects) from the collection's roots; a
/// forwarded object's copy is a block the step made; distinct objects get
/// distinct copies.
let cheney_sound : prop =
  forall (r: real_state) (h: cycle_history) (roots: seq U64.t) (r': real_state).
    (run_invariant r h /\ step r (Minor roots) r') ==>
    (let ms = r.memory.nursery in
     let fwd = (minor_result r roots).Promote.mc_fwd in
     (forall (o: U64.t). Seq.mem o (minor_objects ms) ==>
        (fwd o <> 0UL <==> Seq.mem o (Reach.minor_reachable ms (collector_roots r roots)))) /\
     (forall (o: U64.t). Seq.mem o (minor_objects ms) /\ fwd o <> 0UL ==>
        (exists (x: obj_addr). (x <: U64.t) == fwd o /\ made r r' x)) /\
     (forall (o1 o2: U64.t). Seq.mem o1 (minor_objects ms) /\ Seq.mem o2 (minor_objects ms) /\
        fwd o1 <> 0UL /\ fwd o1 == fwd o2 ==> o1 == o2))

let minor_map_eq (ids: block_id_map) (n: nat) (r: real_state) (roots: seq U64.t) (r': real_state) (x: obj_addr)
  : Lemma (let fwd = (minor_result r roots).Promote.mc_fwd in
           update_block_ids ids n r (Minor roots) r' (Major x) ==
           (if ID.strong_excluded_middle (exists (o: U64.t). forwarded_to r fwd x o)
            then ids (Nursery (ID.indefinite_description_ghost U64.t (forwarded_to r fwd x)))
            else restrict r'.memory ids (Major x)))
  = ()

#push-options "--z3rlimit 60 --fuel 0 --ifuel 1"
let promotes_one (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
                 (roots: seq U64.t) (r': real_state) (a: acc)
  : Lemma (requires cheney_sound /\ mp_pre r h im ids roots r' a)
          (ensures mp_post r h im ids roots r' a)
  = let ms = r.memory.nursery in
    let fwd = (minor_result r roots).Promote.mc_fwd in
    let ids' = update_block_ids ids (Seq.length im.I.objects) r (Minor roots) r' in
    let h' = update_history h r (Minor roots) r' in
    real_shape r h;
    assert (mfacts r h im ids a roots);
    minor_graph r h im ids a roots;
    assert (run_invariant r h);
    let fx (x: obj_addr)
      : Lemma (ids' (Major x) ==
               (if ID.strong_excluded_middle (exists (o: U64.t). forwarded_to r fwd x o)
                then ids (Nursery (ID.indefinite_description_ghost U64.t (forwarded_to r fwd x)))
                else restrict r'.memory ids (Major x)))
      = minor_map_eq ids (Seq.length im.I.objects) r roots r' x in
    // (a) kept blocks keep their ids
    let ka (x: obj_addr) : Lemma (kept h x ==> ids' (Major x) == ids (Major x)) =
      if ID.strong_excluded_middle (kept h x) then begin
        fx x;
        kept_allocated r h x;
        assert (kept h' x);
        kept_allocated r' h' x;
        let nf (o: U64.t) : Lemma (~(forwarded_to r fwd x o)) =
          if ID.strong_excluded_middle (forwarded_to r fwd x o) then
            eliminate exists (y: obj_addr). (y <: U64.t) == fwd o /\ made r r' y
            with assert (y == x)
        in
        FStar.Classical.forall_intro nf
      end in
    FStar.Classical.forall_intro ka;
    // (b) the made blocks hold the promoted objects
    let pb (id: I.obj_id)
      : Lemma ((exists (x: obj_addr). made r r' x /\ ids' (Major x) == Some id) <==> promoted a id) =
      introduce (exists (x: obj_addr). made r r' x /\ ids' (Major x) == Some id) ==> promoted a id
      with eliminate exists (x: obj_addr). made r r' x /\ ids' (Major x) == Some id
      with begin
        fx x;
        if ID.strong_excluded_middle (exists (o: U64.t). forwarded_to r fwd x o) then begin
          let o' = ID.indefinite_description_ghost U64.t (forwarded_to r fwd x) in
          assert (forwarded_to r fwd x o');
          assert (Seq.mem o' (minor_objects ms));
          assert (fwd o' <> 0UL);
          assert (promoted_block ids a o')
        end else
          assert (ids (Major x) == Some id)
      end;
      introduce promoted a id ==> (exists (x: obj_addr). made r r' x /\ ids' (Major x) == Some id)
      with begin
        eliminate exists (n: nat). promo_within a n id
        with promo_nurs a n id;
        eliminate exists (o: U64.t). ids (Nursery o) == Some id
        with begin
          assert (promoted_block ids a o);
          assert (Seq.mem o (minor_objects ms));
          assert (fwd o <> 0UL);
          eliminate exists (x: obj_addr). (x <: U64.t) == fwd o /\ made r r' x
          with begin
            fx x;
            assert (forwarded_to r fwd x o);
            let o' = ID.indefinite_description_ghost U64.t (forwarded_to r fwd x) in
            assert (forwarded_to r fwd x o');
            assert (o' == o)
          end
        end
      end in
    FStar.Classical.forall_intro pb
#pop-options

let promotes_at (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
                (roots: seq U64.t) (r': real_state) (a: acc)
  : Lemma (requires cheney_sound) (ensures minor_promotes_at r h im ids roots r' a)
  = introduce mp_pre r h im ids roots r' a ==> mp_post r h im ids roots r' a
    with promotes_one r h im ids roots r' a

/// **`minor_promotes` follows from the soundness of the Cheney collection.**
let minor_promotes_of_cheney (_: unit) : Lemma (requires cheney_sound) (ensures minor_promotes)
  = introduce forall (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
                     (roots: seq U64.t) (r': real_state) (a: acc).
      minor_promotes_at r h im ids roots r' a
    with promotes_at r h im ids roots r' a

/// ---------------------------------------------------------------------------
/// The Cheney facts (`GC.Gen.Cheney.Soundness`, `GC.Gen.CheneyBFS`)
/// ---------------------------------------------------------------------------

module CS = GC.Gen.Cheney.Soundness
module CB = GC.Gen.CheneyBFS
module CG = GC.Gen.CheneyGeneric
module GI = GC.Gen.Incremental
module GenInv = GC.Gen.HeapInvariant
module Cheney = GC.Gen.Cheney

#push-options "--z3rlimit 60 --fuel 0 --ifuel 1"
let cheney_one (r: real_state) (h: cycle_history) (roots: seq U64.t) (r': real_state)
  : Lemma (requires run_invariant r h /\ step r (Minor roots) r')
          (ensures (let ms = r.memory.nursery in
                    let fwd = (minor_result r roots).Promote.mc_fwd in
                    (forall (o: U64.t). Seq.mem o (minor_objects ms) ==>
                       (fwd o <> 0UL <==> Seq.mem o (Reach.minor_reachable ms (collector_roots r roots)))) /\
                    (forall (o: U64.t). Seq.mem o (minor_objects ms) /\ fwd o <> 0UL ==>
                       (exists (x: obj_addr). (x <: U64.t) == fwd o /\ made r r' x)) /\
                    (forall (o1 o2: U64.t). Seq.mem o1 (minor_objects ms) /\ Seq.mem o2 (minor_objects ms) /\
                       fwd o1 <> 0UL /\ fwd o1 == fwd o2 ==> o1 == o2)))
  = let ms = r.memory.nursery in
    let g = r.memory.major in
    let fp = r.free_list in
    let ph = r.phase in
    let free = GI.phase_free ph in
    let rts = collector_roots r roots in
    let res = minor_result r roots in
    let fwd = res.Promote.mc_fwd in
    let prom = Cheney.cheney_promote ph ms g fp rts in
    assert (res == Cheney.cheney_collect_spec_with ph free ms g fp rts);
    assert (fwd == prom.Promote.fwd_map);
    assert (minor_step r roots r');
    assert (r'.memory.major == res.Promote.mc_major);
    GI.phase_shape_collection ms g fp ph r.scan_pos;
    GenInv.collection_shape_with_elim ph free ms g fp;
    GenInv.minor_heap_shape_elim ms;
    GenInv.major_shape_with_elim ph free g fp;
    CS.promote_pre_of_shape ph free ms g fp;
    CB.cheney_promotes_all_reachable ph ms g fp rts;
    CG.cheney_promote_fwd_targets_not_free ph free ms g fp rts;
    let c1 (o: U64.t) : Lemma (Seq.mem o (minor_objects ms) ==>
                               (fwd o <> 0UL <==> Seq.mem o (Reach.minor_reachable ms rts))) =
      if Seq.mem o (minor_objects ms) then begin
        minor_objects_body_bound ms o;
        if fwd o <> 0UL then CS.cheney_collect_forwarded_reachable ph free ms g fp rts o
      end in
    FStar.Classical.forall_intro c1;
    let c2 (o: U64.t) : Lemma (Seq.mem o (minor_objects ms) /\ fwd o <> 0UL ==>
                               (exists (x: obj_addr). (x <: U64.t) == fwd o /\ made r r' x)) =
      if Seq.mem o (minor_objects ms) && fwd o <> 0UL then begin
        let x : obj_addr = fwd o in
        CS.cheney_collect_new_blocks_stw ph free ms g fp rts x
      end in
    FStar.Classical.forall_intro c2;
    let c3 (o1 o2: U64.t) : Lemma (fwd o1 <> 0UL /\ fwd o1 == fwd o2 ==> o1 == o2) =
      if fwd o1 <> 0UL && fwd o1 = fwd o2 then CS.cheney_collect_fwd_injective ph free ms g fp rts o1 o2 in
    FStar.Classical.forall_intro_2 c3
#pop-options

/// **The Cheney facts hold.**
let cheney_sound_holds (_: unit) : Lemma cheney_sound
  = introduce forall (r: real_state) (h: cycle_history) (roots: seq U64.t) (r': real_state).
      (run_invariant r h /\ step r (Minor roots) r') ==>
      (let ms = r.memory.nursery in
       let fwd = (minor_result r roots).Promote.mc_fwd in
       (forall (o: U64.t). Seq.mem o (minor_objects ms) ==>
          (fwd o <> 0UL <==> Seq.mem o (Reach.minor_reachable ms (collector_roots r roots)))) /\
       (forall (o: U64.t). Seq.mem o (minor_objects ms) /\ fwd o <> 0UL ==>
          (exists (x: obj_addr). (x <: U64.t) == fwd o /\ made r r' x)) /\
       (forall (o1 o2: U64.t). Seq.mem o1 (minor_objects ms) /\ Seq.mem o2 (minor_objects ms) /\
          fwd o1 <> 0UL /\ fwd o1 == fwd o2 ==> o1 == o2))
    with introduce _ ==> _ with cheney_one r h roots r'

/// **`minor_promotes` holds.**
let minor_promotes_holds (_: unit) : Lemma minor_promotes
  = cheney_sound_holds ();
    minor_promotes_of_cheney ()
