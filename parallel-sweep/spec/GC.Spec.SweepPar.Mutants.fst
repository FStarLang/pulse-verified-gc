/// ---------------------------------------------------------------------------
/// GC.Spec.SweepPar.Mutants — deliberately wrong merge/link steps (test only)
///
/// Each mutant breaks one thing the statement depends on.  The test harness
/// must report a difference for every one of them, or it is not able to see
/// the bugs it is meant to find.
///
///   1 no_chain   an all-free segment ends the carried run instead of
///                extending it (runs never span more than one boundary)
///   2 no_merge   trailing and leading runs at a boundary are flushed as two
///                runs
///   3 no_patch   the first linked block keeps its placeholder link (0UL)
///   4 old_head   the first linked block is patched with the head from
///                before the boundary run was flushed
/// ---------------------------------------------------------------------------
module GC.Spec.SweepPar.Mutants

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.SweepPar.Exec
open GC.Spec.SweepPar

let rec link_all_m (m: nat) (g: heap) (carry: run) (fp: U64.t) (rs: list seg)
  : Tot (heap & U64.t) (decreases rs)
  = match rs with
    | [] -> flush_blue_x g carry.fb carry.rw fp
    | r :: rest ->
      let o = r.out in
      if o.all_free then
        if m = 1 then
          let (g1, fp1) = flush_blue_x g carry.fb carry.rw fp in
          link_all_m m g1 o.lead fp1 rest
        else link_all_m m g (join carry o.lead) fp rest
      else
        let (g1, fp1) =
          if m = 2 then
            let (ga, fpa) = flush_blue_x g carry.fb carry.rw fp in
            flush_blue_x ga o.lead.fb o.lead.rw fpa
          else
            let run = join carry o.lead in
            flush_blue_x g run.fb run.rw fp in
        let (g2, fp2) =
          match o.first_link with
          | None -> (g1, fp1)
          | Some a ->
            if m = 3 then (g1, o.local_head)
            else if m = 4 then (patch_link g1 a fp, o.local_head)
            else (patch_link g1 a fp1, o.local_head) in
        link_all_m m g2 o.trail fp2 rest

let sweep_par_m (m: nat) (bs: list nat) (g: heap) : heap & U64.t =
  let rs = sweep_all g (segments bs) in
  link_all_m m (splice_all g rs) no_run 0UL rs
