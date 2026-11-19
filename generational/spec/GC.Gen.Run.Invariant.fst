module GC.Gen.Run.Invariant

open GC.Gen.Run.Step
open GC.Gen.Run.History

module PD = GC.Gen.Run.Invariant.ProgramDefs

/// The definitions restated in `GC.Gen.Run.Invariant.ProgramDefs` are these.
let same_defs (r: real_state) (h: cycle_history) (e: event)
  : Lemma ((GC.Gen.Run.Invariant.Defs.phase_shape r <==> PD.phase_shape r) /\
           (GC.Gen.Run.Invariant.Defs.run_invariant r h <==> PD.run_invariant r h) /\
           (stores_in_kept r h e <==> PD.stores_in_kept r h e))
  = ()

/// Stage 0: the per-step lemmas are admitted; the general step lemma, the
/// induction over a run, and the run forms of losslessness are proved from
/// them.

let initial_run_invariant _ = admit ()

let alloc_keeps_run_invariant r h site tag size init r' = admit ()

let write_keeps_run_invariant r h b i v r' = admit ()

let minor_keeps_run_invariant r h roots r' = admit ()

let start_keeps_run_invariant r h roots r' = admit ()

let slice_keeps_run_invariant r h budget r' = admit ()

let step_keeps_run_invariant r h e r' =
  match e with
  | Alloc site tag size init -> alloc_keeps_run_invariant r h site tag size init r'
  | Write b i v -> write_keeps_run_invariant r h b i v r'
  | Read _ _ | SetRoots _ -> ()
  | Minor roots -> minor_keeps_run_invariant r h roots r'
  | StartCycle roots -> start_keeps_run_invariant r h roots r'
  | Slice budget -> slice_keeps_run_invariant r h budget r'

#push-options "--fuel 1 --ifuel 1"
let along_step (h0: cycle_history) (#r0: real_state) (#es: list event) (#r1: real_state) (rn: run r0 es r1)
  : Lemma (match rn with
           | Done _ -> True
           | Step #_ #_ #r1' rn' e r2 _ ->
               history_along h0 rn == update_history (history_along h0 rn') r1' e r2 /\
               (stores_in_kept_along h0 rn <==>
                stores_in_kept_along h0 rn' /\ stores_in_kept r1' (history_along h0 rn') e))
  = ()
#pop-options

let rec run_invariant_along h0 #r0 #es #r1 rn =
  along_step h0 rn;
  match rn with
  | Done _ -> ()
  | Step #_ #_ #r1' rn' e r2 _ ->
      run_invariant_along h0 rn';
      step_keeps_run_invariant r1' (history_along h0 rn') e r2

let rec same_write_major_fields (g: GC.Spec.Base.heap) (a: FStar.UInt64.t) (init: FStar.Seq.seq FStar.UInt64.t) (i: nat)
  : Lemma (ensures write_major_fields g a init i == PD.write_major_fields g a init i)
          (decreases (FStar.Seq.length init - i))
  = if i >= FStar.Seq.length init then ()
    else
      let p = FStar.UInt64.v a + 8 * i in
      let g' = if p + 8 <= GC.Spec.Base.heap_size && p % 8 = 0
               then GC.Spec.Heap.write_word g (FStar.UInt64.uint_to_t p) (FStar.Seq.index init i) else g in
      same_write_major_fields g' a init (i + 1)

let same_alloc_then_init (r: real_state) (tag: GC.Model.Ideal.tag_t) (size: nat) (init: FStar.Seq.seq FStar.UInt64.t)
  : Lemma (alloc_then_init r tag size init == PD.alloc_then_init r tag size init)
  = let res = GC.Spec.Allocator.Cursor.alloc_phase r.memory.major r.free_list r.phase size tag in
    same_write_major_fields res.GC.Spec.Allocator.heap_out res.GC.Spec.Allocator.obj_out init 0

let alloc_phase_major_alloc_step r tag size init = admit ()

let idle_lossless r h = admit ()

let idle_survives r h = admit ()

let cycle_lossless #es #r rn =
  initial_run_invariant ();
  run_invariant_along (initial_history ()) rn;
  idle_lossless r (history_of_run rn)

let cycle_survives #es #r rn =
  initial_run_invariant ();
  run_invariant_along (initial_history ()) rn;
  idle_survives r (history_of_run rn)
