/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar2.VacBase — the settings the vacuity checks use
///
/// The context of each run, the invariant of each of its states (by
/// `init_inv` and `step_inv`, with nothing computed by hand), and run R0:
/// one range, no roots, which stops and finishes at once and leaves A
/// unreachable.
/// ---------------------------------------------------------------------------
module GC.Spec.MarkPar2.VacBase

open FStar.Seq
module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Graph
open GC.Spec.HeapModel
open GC.Lib.Header
open GC.Spec.MarkPar.Exec
open GC.Spec.MarkPar.Recolour
open GC.Spec.MarkPar.Witness
open GC.Spec.MarkPar2.Witness
open GC.Spec.MarkPar2.Model
open GC.Spec.MarkPar2.Inv
open GC.Spec.MarkPar2.Runs
open GC.Spec.MarkPar2.RunR1
open GC.Spec.MarkPar2.RunR2
open GC.Spec.MarkPar2.RunR3
open GC.Spec.MarkPar2.RunR4

module M1 = GC.Spec.MarkPar.Model
module R = GC.Spec.MarkPar.Roots
module E = GC.Spec.MarkPar2.End
module In = GC.Spec.MarkPar2.Init

let ctx_g5 (_: squash big) (k: cfg) (roots: list obj_addr)
  : Lemma (requires valid_cfg k /\ (forall (r: obj_addr). L.memP r roots ==> r == vA \/ r == obj_B ()))
          (ensures ctx k (g5 ()) roots /\ M1.mark_pre (g5 ()) roots /\ M1.graph_pre (g5 ()) roots)
  = g5_pre_roots () roots;
    R.graph_pre_holds (g5 ()) roots;
    reveal_opaque (`%ctx) (ctx k (g5 ()) roots)

let ctx1 (_: squash big) : Lemma (ctx k1 (g5 ()) (roots1 ())) = ctx_g5 () k1 (roots1 ())
let ctx2 (_: squash big) : Lemma (ctx (k2 ()) (g5 ()) rootsA) = RunR2.own2 (); ctx_g5 () (k2 ()) rootsA
let ctx3 (_: squash big) : Lemma (ctx (k3 ()) (g5 ()) rootsA) = RunR3.own3 (); ctx_g5 () (k3 ()) rootsA
let ctx4 (_: squash big) : Lemma (ctx (k3 ()) (g5 ()) (rootsB ())) = RunR3.own3 (); ctx_g5 () (k3 ()) (rootsB ())

let inv1 (_: squash big)
  : Lemma (let k = k1 in let g = g5 () in let r = roots1 () in
           inv k g r (s0 ()) /\ inv k g r (s1 ()) /\ inv k g r (s2 ()) /\ inv k g r (s3 ()) /\
           inv k g r (s4 ()) /\ inv k g r (s5 ()) /\ inv k g r (s6 ()) /\ inv k g r (s7 ()) /\
           inv k g r (s8 ()) /\ inv k g r (s9 ()) /\ inv k g r (s10 ()) /\ inv k g r (s11 ()))
  = let k = k1 in let g = g5 () in let r = roots1 () in
    ctx1 ();
    In.init_inv k g r;
    E.step_inv k g r (s0 ()) (W 0); E.step_inv k g r (s1 ()) (W 0);
    E.step_inv k g r (s2 ()) (W 0); E.step_inv k g r (s3 ()) (W 0);
    E.step_inv k g r (s4 ()) (W 0); E.step_inv k g r (s5 ()) Main;
    E.step_inv k g r (s6 ()) (W 0); E.step_inv k g r (s7 ()) (W 0);
    E.step_inv k g r (s8 ()) (W 0); E.step_inv k g r (s9 ()) (W 0);
    E.step_inv k g r (s10 ()) Main

let inv2 (_: squash big)
  : Lemma (let k = k2 () in let g = g5 () in let r = rootsA in
           inv k g r (t0 ()) /\ inv k g r (t1 ()) /\ inv k g r (t2 ()) /\ inv k g r (t3 ()) /\
           inv k g r (t4 ()) /\ inv k g r (t5 ()) /\ inv k g r (t6 ()) /\ inv k g r (t7 ()) /\
           inv k g r (t8 ()) /\ inv k g r (t9 ()) /\ inv k g r (t10 ()) /\ inv k g r (t11 ()) /\
           inv k g r (t12 ()) /\ inv k g r (t13 ()) /\ inv k g r (t14 ()) /\ inv k g r (t15 ()) /\
           inv k g r (t16 ()))
  = let k = k2 () in let g = g5 () in let r = rootsA in
    ctx2 ();
    In.init_inv k g r;
    E.step_inv k g r (t0 ()) (W 0); E.step_inv k g r (t1 ()) (W 0);
    E.step_inv k g r (t2 ()) (W 0); E.step_inv k g r (t3 ()) (W 0);
    E.step_inv k g r (t4 ()) (W 1); E.step_inv k g r (t5 ()) (W 1);
    E.step_inv k g r (t6 ()) (W 1); E.step_inv k g r (t7 ()) (W 1);
    E.step_inv k g r (t8 ()) (W 1); E.step_inv k g r (t9 ()) (W 1);
    E.step_inv k g r (t10 ()) (W 0); E.step_inv k g r (t11 ()) (W 0);
    E.step_inv k g r (t12 ()) (W 0); E.step_inv k g r (t13 ()) (W 0);
    E.step_inv k g r (t14 ()) (W 1); E.step_inv k g r (t15 ()) Main

let inv3 (_: squash big)
  : Lemma (let k = k3 () in let g = g5 () in let r = rootsA in
           inv k g r (u0 ()) /\ inv k g r (u1 ()) /\ inv k g r (u2 ()) /\ inv k g r (u3 ()) /\
           inv k g r (u4 ()) /\ inv k g r (u5 ()) /\ inv k g r (u6 ()) /\ inv k g r (u7 ()) /\
           inv k g r (u8 ()) /\ inv k g r (u9 ()) /\ inv k g r (u10 ()) /\ inv k g r (u11 ()) /\
           inv k g r (u12 ()) /\ inv k g r (u13 ()))
  = let k = k3 () in let g = g5 () in let r = rootsA in
    ctx3 ();
    In.init_inv k g r;
    E.step_inv k g r (u0 ()) (W 0); E.step_inv k g r (u1 ()) (W 0);
    E.step_inv k g r (u2 ()) (W 0); E.step_inv k g r (u3 ()) (W 0);
    E.step_inv k g r (u4 ()) (W 0); E.step_inv k g r (u5 ()) (W 1);
    E.step_inv k g r (u6 ()) Main; E.step_inv k g r (u7 ()) (W 1);
    E.step_inv k g r (u8 ()) (W 1); E.step_inv k g r (u9 ()) (W 1);
    E.step_inv k g r (u10 ()) (W 1); E.step_inv k g r (u11 ()) (W 0);
    E.step_inv k g r (u12 ()) Main

let inv4 (_: squash big)
  : Lemma (let k = k3 () in let g = g5 () in let r = rootsB () in
           inv k g r (z0 ()) /\ inv k g r (z1 ()) /\ inv k g r (z2 ()) /\ inv k g r (z3 ()) /\
           inv k g r (z4 ()) /\ inv k g r (z5 ()) /\ inv k g r (z6 ()))
  = let k = k3 () in let g = g5 () in let r = rootsB () in
    ctx4 ();
    In.init_inv k g r;
    E.step_inv k g r (z0 ()) (W 1); E.step_inv k g r (z1 ()) (W 1);
    E.step_inv k g r (z2 ()) (W 1); E.step_inv k g r (z3 ()) (W 1);
    E.step_inv k g r (z4 ()) (W 0); E.step_inv k g r (z5 ()) Main

/// ---------------------------------------------------------------------------
/// Run R0: one range, no roots
/// ---------------------------------------------------------------------------

let r0_0 (_: squash big) : state = init k1 (g5 ()) []
let r0_1 (_: squash big) : state = step k1 (r0_0 ()) (W 0)
let r0_2 (_: squash big) : state = step k1 (r0_1 ()) Main

#push-options "--fuel 3 --ifuel 2"
let r0_eq (_: squash big)
  : Lemma (r0_0 () == { heap = g5 (); wks = [blank]; count = 0; ovf_main = false; finished = false } /\
           r0_2 () == { heap = g5 (); wks = [{ blank with pc = Stopped }]; count = 0; ovf_main = false; finished = true } /\
           run k1 (g5 ()) [] [W 0; Main] == r0_2 ())
  = assert (blanks (nr k1) == [blank])
#pop-options

let inv0 (_: squash big)
  : Lemma (ctx k1 (g5 ()) [] /\ inv k1 (g5 ()) [] (r0_0 ()) /\ inv k1 (g5 ()) [] (r0_1 ()) /\
           inv k1 (g5 ()) [] (r0_2 ()))
  = ctx_g5 () k1 [];
    In.init_inv k1 (g5 ()) [];
    E.step_inv k1 (g5 ()) [] (r0_0 ()) (W 0);
    E.step_inv k1 (g5 ()) [] (r0_1 ()) Main

/// A is not reachable from no roots.
let unreachable0 (_: squash big)
  : Lemma (~(M1.reachable (g5 ()) [] vA))
  = let g = g5 () in
    ctx_g5 () k1 [];
    assert (M1.graph_pre g []);
    let rs' = GC.Spec.HeapGraph.coerce_to_vertex_list (Seq.seq_of_list (M1.root_objs g [])) in
    assert (M1.root_objs g [] == []);
    assert (Seq.length (Seq.seq_of_list ([] #obj_addr)) == 0);
    GC.Spec.DFS.reachable_set_correct (create_graph g) rs';
    FStar.Classical.move_requires (R.coerce_vertex (Seq.seq_of_list (M1.root_objs g []))) vA
