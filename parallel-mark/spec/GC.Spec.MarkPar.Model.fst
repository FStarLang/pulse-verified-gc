/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar.Model — the definitions of the parallel mark model
///
/// Everything `GC.Spec.MarkPar` states its theorems about; that module
/// includes this one.  They are split so that the proof modules can use the
/// definitions and `GC.Spec.MarkPar` can use the proofs.  See
/// `GC.Spec.MarkPar` for the description of the model.
/// ---------------------------------------------------------------------------
module GC.Spec.MarkPar.Model

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

/// A root may be an interior (infix) pointer, and may repeat, as in the
/// roots array `gen_gc` darkens (`check_and_darken_bounded_spec`).  Each is
/// resolved to the object it names, which goes to that object's owner.
/// Repeats are kept: the second Take of an object finds it non-white.
let rec owned_roots (cs: list nat) (g: heap) (i: nat) (xs: list obj_addr)
  : Tot (list obj_addr) (decreases xs)
  = match xs with
    | [] -> []
    | x :: rest ->
      let c = resolve_x x g in
      if owner cs c = i then c :: owned_roots cs g i rest else owned_roots cs g i rest

let rec make_workers (cs: list nat) (g: heap) (roots: list obj_addr) (i: nat) (n: nat)
  : Tot (list worker) (decreases n)
  = if n = 0 then []
    else { work = []; inbox = owned_roots cs g i roots; scan = None }
         :: make_workers cs g roots (i + 1) (n - 1)

let init (cs: list nat) (g: heap) (roots: list obj_addr) : state =
  { heap = g; workers = make_workers cs g roots 0 (nranges cs); net = [] }

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

/// The objects the roots name: each root resolved, repeats removed.
let rec dedup (l: list obj_addr) : Tot (list obj_addr) (decreases l) =
  match l with
  | [] -> []
  | x :: rest -> if L.mem x rest then dedup rest else x :: dedup rest

let rec resolve_all (g: heap) (l: list obj_addr) : GTot (list obj_addr) (decreases l) =
  match l with
  | [] -> []
  | x :: rest -> resolve_object x g :: resolve_all g rest

let rec resolve_all_x (g: heap) (l: list obj_addr)
  : Tot (r:list obj_addr{r == resolve_all g l}) (decreases l)
  = match l with
    | [] -> []
    | x :: rest -> resolve_x x g :: resolve_all_x g rest

let root_objs (g: heap) (roots: list obj_addr) : GTot (list obj_addr) =
  dedup (resolve_all g roots)

let root_objs_x (g: heap) (roots: list obj_addr)
  : r:list obj_addr{r == root_objs g roots}
  = dedup (resolve_all_x g roots)

/// Greying the named objects and marking from them is what `gen_gc`'s
/// darkening followed by the mark does, up to the order of the stack.
let sequential_mark (g: heap) (roots: list obj_addr) : GTot heap =
  let rs = root_objs g roots in
  Mark.mark (grey_all g rs) (Seq.seq_of_list rs)

let sequential_mark_x (g: heap) (roots: list obj_addr)
  : r:heap{r == sequential_mark g roots}
  = let rs = root_objs_x g roots in
    mark_x (grey_all_x g rs) (Seq.seq_of_list rs)

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
  (forall (r: obj_addr). L.memP r roots ==>
     Seq.mem (resolve_object r g) (objects zero_addr g) /\
     is_white (resolve_object r g) g)

/// The graph hypotheses of `end_to_end_correctness`, for the reachable roots.
let graph_pre (g: heap) (roots: list obj_addr) : prop =
  let graph = create_graph g in
  let roots' = HeapGraph.coerce_to_vertex_list (Seq.seq_of_list (root_objs g roots)) in
  graph_wf graph /\ is_vertex_set roots' /\ subset_vertices roots' graph.vertices

let reachable (g: heap) (roots: list obj_addr) (x: obj_addr) : prop =
  graph_pre g roots /\
  Seq.mem x (reachable_set (create_graph g)
                           (HeapGraph.coerce_to_vertex_list (Seq.seq_of_list (root_objs g roots))))

/// ---------------------------------------------------------------------------
/// Termination
/// ---------------------------------------------------------------------------

/// The fields a worker will look at once it pops x.
let fields_to_scan (x: obj_addr) (g: heap) : nat =
  if is_no_scan_x x g then 0 else U64.v (wosize_x x g)

/// The work still to do, counted in steps:
///   a white object       2 + 3f   (grey and push it, pop it, its f fields)
///   an object on a work list   1 + 3f   (pop it, its f fields)
///   a field not yet scanned  3   (scan it, deliver the message it may send,
///                                 take it from the inbox)
///   a message in transit     2   (deliver it, take it)
///   an inbox entry           1   (take it)
/// Every effective step lowers it by at least one: greying a white object
/// turns 2 + 3f into 1 + 3f, popping turns 1 + 3f into 3f, a scan turns 3
/// into at most 2, a delivery turns 2 into 1, and a Take removes 1.
let rec white_weight (g: heap) (xs: list obj_addr) : Tot nat (decreases xs) =
  match xs with
  | [] -> 0
  | x :: rest ->
    (if is_white_x x g then 2 + 3 * fields_to_scan x g else 0) + white_weight g rest

let rec work_weight (g: heap) (xs: list obj_addr) : Tot nat (decreases xs) =
  match xs with
  | [] -> 0
  | x :: rest -> 1 + 3 * fields_to_scan x g + work_weight g rest

let scan_weight (sc: option scanning) : nat =
  match sc with
  | None -> 0
  | Some sc -> if U64.v sc.snext <= U64.v sc.sws then 3 * (U64.v sc.sws - U64.v sc.snext + 1) else 0

let rec workers_weight (g: heap) (ws: list worker) : Tot nat (decreases ws) =
  match ws with
  | [] -> 0
  | w :: rest ->
    work_weight g w.work + scan_weight w.scan + L.length w.inbox + workers_weight g rest

let measure (s: state) : nat =
  white_weight s.heap (Seq.seq_to_list (objects_x zero_addr s.heap))
  + workers_weight s.heap s.workers
  + 2 * L.length s.net

/// The steps of a schedule that change something.
let rec effective_steps (cs: list nat) (s: state) (sched: list event)
  : Tot nat (decreases sched)
  = match sched with
    | [] -> 0
    | e :: rest ->
      (if L.mem e (enabled s) then 1 else 0) + effective_steps cs (step cs s e) rest
