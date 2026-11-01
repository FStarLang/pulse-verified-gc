/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar — parallel mark by ownership: model and statement
///
/// The heap is cut into k address ranges.  Range i is worker i's.  An object
/// belongs to the range holding its header; an interior (infix) pointer is
/// first resolved to its parent closure.  Each worker has its own work list
/// and its own inbox, and writes the colour only of objects it owns:
///
///   Pop i      worker i pops x from its work list and blackens it; it then
///              scans x's fields one at a time (unless x is no-scan or has
///              no fields)
///   Scan i     worker i looks at the next field of the object it is
///              scanning.  A pointer is resolved to the object `c` it names.
///              If i owns c and c is white, i greys it and pushes it.  If
///              another range owns c, i sends c's address to that range.
///   Take i     worker i takes the first address in its inbox, and greys
///              and pushes it if it is white
///   Deliver j  the j-th message in transit reaches its range's inbox
///
/// Messages in transit are a list, and any of them may be delivered next, so
/// delivery may reorder messages.  Each root starts in its owner's inbox.
/// A run is a schedule: any list of events.  An event that is not enabled
/// (popping an empty work list, say) changes nothing, so every list is a
/// schedule and every interleaving is some list.  Marking has ended when
/// every work list, every inbox and the network are empty and no worker is
/// part-way through an object (`quiescent`).
///
/// The theorem, `mark_par_correct`: for every cut list and every schedule,
/// if the run has ended, its heap is the sequential mark's, byte for byte.
/// ---------------------------------------------------------------------------
module GC.Spec.MarkPar

open FStar.Seq
module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot
open FStar.List.Tot { (@) }

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Graph
open GC.Spec.HeapModel
open GC.Spec.DFS
open GC.Spec.MarkPar.Exec

module HeapGraph = GC.Spec.HeapGraph
module Mark = GC.Spec.Mark

/// ---------------------------------------------------------------------------
/// Ranges
/// ---------------------------------------------------------------------------

/// `cs` lists the k-1 interior cuts.  Range 0 is [zero_addr, c1), range i is
/// [c_i, c_{i+1}), and range k-1 is [c_{k-1}, heap_size).  Cuts may be at
/// any address: they need not be aligned, nor fall on a header.
let rec valid_cuts_from (prev: nat) (cs: list nat) : Tot bool (decreases cs) =
  match cs with
  | [] -> true
  | c :: rest -> prev < c && c < heap_size && valid_cuts_from c rest

let valid_cuts (cs: list nat) : bool = valid_cuts_from (U64.v zero_addr) cs

let nranges (cs: list nat) : pos = L.length cs + 1

let rec count_le (cs: list nat) (a: nat) : nat =
  match cs with
  | [] -> 0
  | c :: rest -> (if c <= a then 1 else 0) + count_le rest a

/// The range holding x's header.
let owner (cs: list nat) (x: obj_addr) : nat = count_le cs (U64.v (hd_address x))

/// ---------------------------------------------------------------------------
/// State
/// ---------------------------------------------------------------------------

/// Worker part-way through object `sobj`: field `snext` is next, of `sws`.
type scanning = {
  sobj  : obj_addr;
  snext : i:U64.t{U64.v i >= 1};
  sws   : U64.t;
}

type worker = {
  work  : list obj_addr;        (* grey objects to scan; head is next *)
  inbox : list obj_addr;        (* delivered addresses; head is next *)
  scan  : option scanning;
}

type msg = {
  dest : nat;
  addr : obj_addr;
}

noeq type state = {
  heap    : heap;
  workers : list worker;        (* worker i is element i *)
  net     : list msg;           (* sent, not yet delivered *)
}

type event =
  | Pop     of nat
  | Scan    of nat
  | Take    of nat
  | Deliver of nat

/// The worker an event belongs to.  A delivery belongs to no worker; it
/// never touches the heap.
let actor (e: event) : nat =
  match e with
  | Pop i | Scan i | Take i -> i
  | Deliver _ -> 0

/// ---------------------------------------------------------------------------
/// List helpers
/// ---------------------------------------------------------------------------

let rec nth (#a: Type) (l: list a) (i: nat) : option a =
  match l with
  | [] -> None
  | x :: rest -> if i = 0 then Some x else nth rest (i - 1)

let rec set_nth (#a: Type) (l: list a) (i: nat) (v: a) : list a =
  match l with
  | [] -> []
  | x :: rest -> if i = 0 then v :: rest else x :: set_nth rest (i - 1) v

let rec remove_nth (#a: Type) (l: list a) (i: nat) : list a =
  match l with
  | [] -> []
  | x :: rest -> if i = 0 then rest else x :: remove_nth rest (i - 1)

/// ---------------------------------------------------------------------------
/// The initial state
/// ---------------------------------------------------------------------------

let rec owned_by (cs: list nat) (i: nat) (xs: list obj_addr) : Tot (list obj_addr) (decreases xs) =
  match xs with
  | [] -> []
  | x :: rest -> if owner cs x = i then x :: owned_by cs i rest else owned_by cs i rest

let rec make_workers (cs: list nat) (roots: list obj_addr) (i: nat) (n: nat)
  : Tot (list worker) (decreases n)
  = if n = 0 then []
    else { work = []; inbox = owned_by cs i roots; scan = None }
         :: make_workers cs roots (i + 1) (n - 1)

let init (cs: list nat) (g: heap) (roots: list obj_addr) : state =
  { heap = g; workers = make_workers cs roots 0 (nranges cs); net = [] }

/// ---------------------------------------------------------------------------
/// One step
/// ---------------------------------------------------------------------------

let next_field (sc: scanning) : option scanning =
  if U64.v sc.snext < U64.v sc.sws
  then Some { sc with snext = U64.add sc.snext 1UL }
  else None

/// Worker i, white-checking and greying an object it owns.
let grey_push (g: heap) (w: worker) (x: obj_addr) : heap & worker =
  if is_white_x x g then (makeGray_x x g, { w with work = x :: w.work })
  else (g, w)

let step (cs: list nat) (s: state) (e: event) : state =
  match e with
  | Pop i ->
    (match nth s.workers i with
     | Some w ->
       (match w.scan, w.work with
        | None, x :: rest ->
          let ws = wosize_x x s.heap in
          let sc =
            if is_no_scan_x x s.heap || U64.v ws = 0 then None
            else Some { sobj = x; snext = 1UL; sws = ws } in
          { s with heap = makeBlack_x x s.heap;
                   workers = set_nth s.workers i { w with work = rest; scan = sc } }
        | _ -> s)
     | None -> s)
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
            let o = owner cs c in
            if o = i then
              let (g', w') = grey_push s.heap w0 c in
              { s with heap = g'; workers = set_nth s.workers i w' }
            else
              { s with workers = set_nth s.workers i w0;
                       net = s.net @ [{ dest = o; addr = c }] }
          end else
            { s with workers = set_nth s.workers i w0 }
        | None -> s)
     | None -> s)
  | Take i ->
    (match nth s.workers i with
     | Some w ->
       (match w.inbox with
        | x :: rest ->
          let (g', w') = grey_push s.heap { w with inbox = rest } x in
          { s with heap = g'; workers = set_nth s.workers i w' }
        | [] -> s)
     | None -> s)
  | Deliver j ->
    (match nth s.net j with
     | Some m ->
       (match nth s.workers m.dest with
        | Some w ->
          { s with workers = set_nth s.workers m.dest { w with inbox = w.inbox @ [m.addr] };
                   net = remove_nth s.net j }
        | None -> s)
     | None -> s)

let rec run_from (cs: list nat) (s: state) (sched: list event)
  : Tot state (decreases sched)
  = match sched with
    | [] -> s
    | e :: rest -> run_from cs (step cs s e) rest

let run (cs: list nat) (g: heap) (roots: list obj_addr) (sched: list event) : state =
  run_from cs (init cs g roots) sched

/// ---------------------------------------------------------------------------
/// The end of marking
/// ---------------------------------------------------------------------------

let idle (w: worker) : bool = Nil? w.work && Nil? w.inbox && None? w.scan

let quiescent (s: state) : bool = Nil? s.net && L.for_all idle s.workers

/// The events that change something.  Not used by the theorem; the test
/// draws from it, and checks it is empty exactly when `quiescent` holds.
let rec worker_events (i: nat) (ws: list worker) : Tot (list event) (decreases ws) =
  match ws with
  | [] -> []
  | w :: rest ->
    (if Some? w.scan then [Scan i] else if Cons? w.work then [Pop i] else [])
    @ (if Cons? w.inbox then [Take i] else [])
    @ worker_events (i + 1) rest

let rec deliver_events (j: nat) (n: list msg) : Tot (list event) (decreases n) =
  match n with
  | [] -> []
  | _ :: rest -> Deliver j :: deliver_events (j + 1) rest

let enabled (s: state) : list event =
  worker_events 0 s.workers @ deliver_events 0 s.net

/// ---------------------------------------------------------------------------
/// The sequential reference
/// ---------------------------------------------------------------------------

/// The sequential collector greys the roots, puts them on its stack, and
/// runs `GC.Spec.Mark.mark`.
let rec grey_all (g: heap) (roots: list obj_addr) : GTot heap (decreases roots) =
  match roots with
  | [] -> g
  | r :: rest -> grey_all (makeGray r g) rest

let rec grey_all_x (g: heap) (roots: list obj_addr)
  : Tot (r:heap{r == grey_all g roots}) (decreases roots)
  = match roots with
    | [] -> g
    | r :: rest -> grey_all_x (makeGray_x r g) rest

let sequential_mark (g: heap) (roots: list obj_addr) : GTot heap =
  Mark.mark (grey_all g roots) (Seq.seq_of_list roots)

let sequential_mark_x (g: heap) (roots: list obj_addr)
  : r:heap{r == sequential_mark g roots}
  = mark_x (grey_all_x g roots) (Seq.seq_of_list roots)

/// ---------------------------------------------------------------------------
/// The statement
/// ---------------------------------------------------------------------------

/// The sequential mark's precondition (`GC.Spec.Correctness.
/// end_to_end_correctness`), with the roots white rather than already grey
/// and on the stack: here the roots start in inboxes, and greying them is
/// the owners' job.
let mark_pre (g: heap) (roots: list obj_addr) : prop =
  well_formed_heap g /\
  Mark.noGreyObjects g /\
  Mark.no_black_objects g /\
  Mark.no_pointer_to_blue g /\
  L.noRepeats roots /\
  (forall (r: obj_addr). L.memP r roots ==>
     Seq.mem r (objects zero_addr g) /\ is_white r g)

val mark_par_correct (cs: list nat) (g: heap) (roots: list obj_addr) (sched: list event)
  : Lemma (requires mark_pre g roots /\ valid_cuts cs /\
                    quiescent (run cs g roots sched))
          (ensures (run cs g roots sched).heap == sequential_mark g roots)

let mark_par_correct cs g roots sched = admit ()

/// The same conclusion said without the sequential mark: exactly the objects
/// reachable from the roots are black, each is the original header made
/// black, and every other word of the heap is unchanged.  The graph
/// hypotheses are `end_to_end_correctness`'s.
let graph_pre (g: heap) (roots: list obj_addr) : prop =
  let graph = create_graph g in
  let roots' = HeapGraph.coerce_to_vertex_list (Seq.seq_of_list roots) in
  graph_wf graph /\ is_vertex_set roots' /\ subset_vertices roots' graph.vertices

let reachable (g: heap) (roots: list obj_addr) (x: obj_addr) : prop =
  graph_pre g roots /\
  Seq.mem x (reachable_set (create_graph g)
                           (HeapGraph.coerce_to_vertex_list (Seq.seq_of_list roots)))

val mark_par_reachable (cs: list nat) (g: heap) (roots: list obj_addr) (sched: list event)
  : Lemma (requires mark_pre g roots /\ valid_cuts cs /\
                    quiescent (run cs g roots sched) /\
                    graph_pre g roots)
          (ensures (let h = (run cs g roots sched).heap in
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==>
                       (is_black x h <==> reachable g roots x)) /\
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr g) /\ reachable g roots x ==>
                       read_word h (hd_address x) == read_word (makeBlack x g) (hd_address x)) /\
                    (forall (a: hp_addr).
                       (forall (x: obj_addr). Seq.mem x (objects zero_addr g) /\ reachable g roots x ==>
                          a <> hd_address x) ==>
                       read_word h a == read_word g a)))

let mark_par_reachable cs g roots sched = admit ()

/// Only the owner writes a colour: from any state a run reaches, the next
/// step changes the heap only in the header of an enumerated object that the
/// acting worker owns.
val step_writes_own (cs: list nat) (g: heap) (roots: list obj_addr) (sched: list event)
    (e: event) (a: hp_addr)
  : Lemma (requires mark_pre g roots /\ valid_cuts cs /\
                    (let s = run cs g roots sched in
                     read_word (step cs s e).heap a <> read_word s.heap a))
          (ensures exists (x: obj_addr).
                     a == hd_address x /\ Seq.mem x (objects zero_addr g) /\
                     owner cs x == actor e)

let step_writes_own cs g roots sched e a = admit ()
