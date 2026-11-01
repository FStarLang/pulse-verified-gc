/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar.Mutants — deliberately wrong parallel marks (test only)
///
/// Each mutant breaks one rule the design depends on.  The test harness must
/// catch every one of them, or it is not able to see the bugs it is meant to
/// find.
///
///   1 foreign_grey   a worker that finds a white child in another range
///                    greys it itself, then sends it.  The owner then finds
///                    it grey, does not push it, and nobody scans it.
///   2 overwrite      an inbox is one slot: a delivery into a non-empty
///                    inbox replaces its last address, dropping a message.
///   3 route_raw      a child is routed by the range of the raw field value,
///                    not of its resolved parent closure.  An infix pointer
///                    whose header lies in another range than its closure's
///                    is then greyed by a worker that does not own it.
///   4 early_stop     termination ignores messages still in transit: the
///                    run ends when work lists and inboxes are empty and no
///                    worker is scanning (`quiescent_m 4`).
///
/// Mutant 0 is the model itself, written again here; the test checks it
/// agrees with `GC.Spec.MarkPar.step`.
/// ---------------------------------------------------------------------------
module GC.Spec.MarkPar.Mutants

open FStar.Seq
module U64 = FStar.UInt64
module L = FStar.List.Tot
open FStar.List.Tot { (@) }

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.MarkPar.Exec
open GC.Spec.MarkPar.Model

module HeapGraph = GC.Spec.HeapGraph

let step_m (m: nat) (cs: list nat) (s: state) (e: event) : state =
  match e with
  | Scan i ->
    (match nth s.workers i with
     | Some w ->
       (match w.scan with
        | Some sc ->
          let w0 = { w with scan = next_field sc } in
          let v = get_field_x s.heap sc.sobj sc.snext in
          if HeapGraph.is_pointer_field v then begin
            HeapGraph.is_pointer_field_is_obj_addr v;
            let c = resolve_x v s.heap in
            let o = if m = 3 then owner cs v else owner cs c in
            if o = i then
              let (g', w') = grey_push s.heap w0 c in
              { s with heap = g'; workers = set_nth s.workers i w' }
            else
              let g' =
                if m = 1 && is_white_x c s.heap then makeGray_x c s.heap else s.heap in
              { s with heap = g';
                       workers = set_nth s.workers i w0;
                       net = s.net @ [{ dest = o; addr = c }] }
          end else
            { s with workers = set_nth s.workers i w0 }
        | None -> s)
     | None -> s)
  | Deliver j ->
    if m = 2 then
      (match nth s.net j with
       | Some ms ->
         (match nth s.workers ms.dest with
          | Some w ->
            let inbox' =
              match w.inbox with
              | [] -> [ms.addr]
              | _ -> L.init w.inbox @ [ms.addr] in
            { s with workers = set_nth s.workers ms.dest { w with inbox = inbox' };
                     net = remove_nth s.net j }
          | None -> s)
       | None -> s)
    else step cs s e
  | _ -> step cs s e

let quiescent_m (m: nat) (s: state) : bool =
  if m = 4 then L.for_all idle s.workers else quiescent s
