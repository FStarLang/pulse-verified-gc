/// ---------------------------------------------------------------------------
/// GC.Spec.Top.Stw - T2, as propositions: a cycle frees what a
/// stop-the-world collection at its start frees
/// ---------------------------------------------------------------------------
///
/// Design doc §16.7.  For a cycle `s..j` of a run `es`, the stop-the-world
/// run `es'` is `es` up to `s`, then a whole cycle with no other event:
/// `EStart`, slices, `EHandover`, sweep steps, `EEnd` (`stw_run`).  T2: it
/// exists, it is a run, and the two runs free the same objects; the
/// stop-the-world run keeps exactly what was reachable at `s`, and the
/// incremental one keeps those and the objects allocated during the cycle
/// (`stw_equiv`).  `t2` assumes the contracts (`components_ok`) and builds
/// `es'`; `t2_local` takes the contracts only at the steps of both runs, and
/// `es'` as given.

module GC.Spec.Top.Stw

open GC.Spec.Top.Heap
open GC.Spec.Top.Rep
open GC.Spec.Top.Iface
open GC.Spec.Top.Run
module L = FStar.List.Tot

let rec rep (k: nat) (e: event) : list event = if k = 0 then [] else e :: rep (k - 1) e

/// A whole cycle and nothing else: start, `a` slices, the handover, `b`
/// sweep steps, the end.
let stw_tail (a b: nat) : list event =
  EStart :: L.append (rep a ESlice) (EHandover :: L.append (rep b ESweep) [EEnd])

/// `es'` is `es` up to `s`, then a whole cycle and nothing else.
let stw_run (es: list event) (s: nat) (es': list event) : prop =
  s <= L.length es /\ (exists (a b: nat). es' == L.append (take s es) (stw_tail a b))

/// The last event of a run (of an empty one, 0: `is_cycle` then fails).
let last (es: list event) : nat = if L.length es > 0 then L.length es - 1 else 0

/// The two runs, for the cycle `s..j` of `es`; the cycle of `es'` ends at
/// its last event `j'`.
let stw_equiv (c: comps) (n ny: nat) (es: list event) (s j: nat) (es': list event) : prop =
  let j' = last es' in
  let x0 = at c n ny es s in
  let xe = at c n ny es j in
  let xf = at c n ny es (j + 1) in
  let xf' = at c n ny es' (j' + 1) in
  is_cycle es' s j' /\
  (* the runs agree up to s *)
  (forall (i: nat). i <= s ==> at c n ny es' i == at c n ny es i) /\
  (* they free the same objects *)
  (forall (o: nat). freed_in c n ny es s j o <==> freed_in c n ny es' s j' o) /\
  (* the stop-the-world run keeps exactly what was reachable at s *)
  (forall (o: nat). in_use_c xf' o == true <==> reachable (wv x0) o) /\
  (* the incremental run keeps those, and the objects allocated during the
     cycle (floating garbage of kind (ii), §2.3) *)
  (forall (o: nat). in_use_c xf o == true <==> (in_use_c xf' o == true \/ xe.allocd o))

/// T2 with the contracts at the steps taken, by both runs.
let t2_local (c: comps) (sty: style) : prop =
  faithful c.r ==>
  (forall (n ny: nat) (es es': list event) (s j: nat).
     run_ok c sty n ny es /\ run_hyps c n ny es /\ is_cycle es s j /\
     stw_run es s es' /\ run_ok c sty n ny es' /\ run_hyps c n ny es' ==>
     stw_equiv c n ny es s j es')

/// T2: the stop-the-world run exists, is a run, and is equivalent.
let t2 (c: comps) (sty: style) : prop =
  components_ok c ==>
  (forall (n ny: nat) (es: list event) (s j: nat).
     run_ok c sty n ny es /\ is_cycle es s j ==>
     (exists (es': list event). stw_run es s es' /\ run_ok c sty n ny es' /\ stw_equiv c n ny es s j es'))
