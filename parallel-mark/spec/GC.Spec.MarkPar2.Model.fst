/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar2.Model — the parallel mark of docs/parallel-mark-design.md
///
/// The definitions every Stage 3 theorem is about; `GC.Spec.MarkPar2`
/// states the theorems.  The heap is cut into ranges as in Stage 1
/// (`GC.Spec.MarkPar.Model`), and an object belongs to the range holding its
/// header.  Each worker i has
///   * a stack of at most `cap_s` objects, its own;
///   * an inbox of at most `cap_q` raw addresses, which anyone appends to;
///   * a program counter, `pc`, saying where it is in the loop of the design;
///   * an overflow flag.
/// One counter, `count` (the design's work_in_flight), is shared by all.
///
/// A worker is a deterministic program: an event `W i` runs worker i's next
/// step.  Each step does at most one shared action (a send under the
/// target's lock, a take under its own lock, or one atomic update or read of
/// the counter) plus actions on its own stack, headers and pc, which no other
/// worker sees.  So any interleaving of the real workers is a schedule of
/// these steps.  The design's
///
///   pop; scan(x); work_in_flight -= 1
///
/// is a Loop step (pop, blacken), one Scan step per field (route the
/// field), and a Finish step (subtract 1).  try_take is a Loop step that
/// moves the head of the inbox to `Got v`; accept(v) is the Got step; the
/// subtraction is again a Finish step.  A try_take that finds the inbox
/// empty is a Loop step of its own, to `Idle`; the atomic read of the
/// counter is the Idle step after it: at 0 the worker stops, otherwise it
/// goes back to Loop and looks again.  A message may arrive between the two.
///
/// `Main` is the main thread between rounds.  It runs only when every worker
/// has stopped (the stop barrier).  It checks every overflow flag; if none
/// is set, marking is done.  Otherwise it clears them and runs the fix-up:
/// one walk over the heap's objects, in address order.  If the fix-up
/// pushed nothing, marking is done; otherwise `count` is set to the number
/// pushed and every worker starts again (the start barrier).  Setup, in
/// `init`, darkens the roots as `check_and_darken_bounded_spec` does.
///
/// Everything is computable: the test runs this model as it is.
/// ---------------------------------------------------------------------------
module GC.Spec.MarkPar2.Model

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
open GC.Spec.MarkPar.Exec

module HeapGraph = GC.Spec.HeapGraph
module Mark = GC.Spec.Mark
module M1 = GC.Spec.MarkPar.Model

/// ---------------------------------------------------------------------------
/// Configuration
/// ---------------------------------------------------------------------------

/// The cut list (as in Stage 1) and the two capacities.
type cfg = {
  cs    : list nat;
  cap_s : nat;            (* S: stack capacity, per worker *)
  cap_q : nat;            (* Q: inbox capacity, per worker *)
}

/// The design needs S >= 1; Q may be 0.
let valid_cfg (k: cfg) : bool = M1.valid_cuts k.cs && k.cap_s >= 1

let nr (k: cfg) : pos = M1.nranges k.cs

/// The range holding x's header.
let own (k: cfg) (x: obj_addr) : nat = M1.owner k.cs x

/// ---------------------------------------------------------------------------
/// State
/// ---------------------------------------------------------------------------

type pc =
  | Loop                              (* at the top of the loop *)
  | Scan of M1.scanning               (* x popped and black; field snext next *)
  | Got of obj_addr                   (* taken from the inbox, not yet accepted *)
  | Idle                              (* found the inbox empty; reads the counter next *)
  | Finish                            (* handled; work_in_flight -= 1 next *)
  | Stopped                           (* read 0; waiting at the stop barrier *)

type wk = {
  stack : list obj_addr;              (* head is the top *)
  inbox : list obj_addr;              (* head is the oldest *)
  pc    : pc;
  ovf   : bool;                       (* overflow[i] *)
}

noeq type state = {
  heap     : heap;
  wks      : list wk;                 (* worker i is element i *)
  count    : nat;                     (* work_in_flight *)
  ovf_main : bool;
  finished : bool;                    (* marking is done *)
}

type event =
  | W of nat                          (* worker i's next step *)
  | Main                              (* the main thread, between rounds *)

let set_ovf (s: state) (i: nat) : state =
  match M1.nth s.wks i with
  | Some w -> { s with wks = M1.set_nth s.wks i { w with ovf = true } }
  | None -> s

/// ---------------------------------------------------------------------------
/// The worker's actions (the design's send, accept and route)
/// ---------------------------------------------------------------------------

/// send(j, v): under inbox[j]'s lock.  A full inbox drops v and sets the
/// sender's flag; otherwise the counter goes up before v is appended.
let send (k: cfg) (s: state) (me j: nat) (v: obj_addr) : state =
  match M1.nth s.wks j with
  | Some wj ->
    if L.length wj.inbox >= k.cap_q then set_ovf s me
    else { s with wks = M1.set_nth s.wks j { wj with inbox = wj.inbox @ [v] };
                  count = s.count + 1 }
  | None -> s

/// The end of accept: c is mine.  A white c is greyed; a full stack leaves
/// it grey and sets the flag; otherwise the counter goes up and c is pushed.
let grey_push (k: cfg) (s: state) (me: nat) (c: obj_addr) : state =
  if is_white_x c s.heap then
    match M1.nth s.wks me with
    | Some w ->
      let h' = makeGray_x c s.heap in
      if L.length w.stack >= k.cap_s
      then { s with heap = h'; wks = M1.set_nth s.wks me { w with ovf = true } }
      else { s with heap = h'; wks = M1.set_nth s.wks me { w with stack = c :: w.stack };
                    count = s.count + 1 }
    | None -> s
  else s

/// accept(v): v's header word is mine.  It is read to resolve an infix
/// pointer to its closure c; a closure owned elsewhere is sent on.
let accept (k: cfg) (s: state) (me: nat) (v: obj_addr) : state =
  let c = resolve_x v s.heap in
  let o = own k c in
  if o <> me then send k s me o c else grey_push k s me c

/// route(v): by v's own header address, with no memory read.
let route (k: cfg) (s: state) (me: nat) (v: obj_addr) : state =
  let o = own k v in
  if o = me then accept k s me v else send k s me o v

/// ---------------------------------------------------------------------------
/// One worker step
/// ---------------------------------------------------------------------------

let wstep (k: cfg) (s: state) (i: nat) : state =
  match M1.nth s.wks i with
  | None -> s
  | Some w ->
    match w.pc with
    | Loop ->
      (match w.stack with
       | x :: rest ->
         let ws = wosize_x x s.heap in
         let pc' = if is_no_scan_x x s.heap || U64.v ws = 0 then Finish
                   else Scan { M1.sobj = x; M1.snext = 1UL; M1.sws = ws } in
         { s with heap = makeBlack_x x s.heap;
                  wks = M1.set_nth s.wks i { w with stack = rest; pc = pc' } }
       | [] ->
         (match w.inbox with
          | v :: rest -> { s with wks = M1.set_nth s.wks i { w with inbox = rest; pc = Got v } }
          | [] -> { s with wks = M1.set_nth s.wks i { w with pc = Idle } }))
    | Idle ->
      { s with wks = M1.set_nth s.wks i { w with pc = if s.count = 0 then Stopped else Loop } }
    | Scan sc ->
      let pc' = match M1.next_field sc with Some sc' -> Scan sc' | None -> Finish in
      let s0 = { s with wks = M1.set_nth s.wks i { w with pc = pc' } } in
      let v = get_field_x s.heap sc.M1.sobj sc.M1.snext in
      if HeapGraph.is_pointer_field v then begin
        HeapGraph.is_pointer_field_is_obj_addr v;
        route k s0 i v
      end else s0
    | Got v -> accept k { s with wks = M1.set_nth s.wks i { w with pc = Finish } } i v
    | Finish ->
      { s with wks = M1.set_nth s.wks i { w with pc = Loop };
               count = if s.count > 0 then s.count - 1 else 0 }
    | Stopped -> s

/// ---------------------------------------------------------------------------
/// Setup and fix-up, on the main thread
/// ---------------------------------------------------------------------------

/// The main thread's view while it walks or darkens: the heap, the workers,
/// overflow_main, and the number of entries pushed.
noeq type fx = {
  fh  : heap;
  fws : list wk;
  fom : bool;
  fn  : nat;
}

/// Push x on its owner's stack, or set overflow_main if it is full.
let push_fx (k: cfg) (f: fx) (x: obj_addr) : fx =
  let o = own k x in
  match M1.nth f.fws o with
  | Some w ->
    if L.length w.stack >= k.cap_s then { f with fom = true }
    else { f with fws = M1.set_nth f.fws o { w with stack = x :: w.stack }; fn = f.fn + 1 }
  | None -> f

/// Requirement 6: resolve an infix root to its closure; grey and push it
/// only if it is white.  (Roots are object addresses here, as in Stage 1:
/// skipping a value that is not a pointer is the caller's.)
let darken (k: cfg) (f: fx) (r: obj_addr) : fx =
  let c = resolve_x r f.fh in
  if is_white_x c f.fh then push_fx k { f with fh = makeGray_x c f.fh } c else f

let rec setup (k: cfg) (f: fx) (roots: list obj_addr) : Tot fx (decreases roots) =
  match roots with
  | [] -> f
  | r :: rest -> setup k (darken k f r) rest

let blank : wk = { stack = []; inbox = []; pc = Loop; ovf = false }

let rec blanks (n: nat) : Tot (list wk) (decreases n) =
  if n = 0 then [] else blank :: blanks (n - 1)

let init (k: cfg) (g: heap) (roots: list obj_addr) : state =
  let f = setup k { fh = g; fws = blanks (nr k); fom = false; fn = 0 } roots in
  { heap = f.fh; wks = f.fws; count = f.fn; ovf_main = f.fom; finished = false }

/// Fix-up step 4, for the value v of one field of the black object y at the
/// walk's position: a white object it names is greyed, and pushed only if it
/// lies below y.  One above y is pushed by step 3 when the walk reaches it.
let fix_child (k: cfg) (y: obj_addr) (f: fx) (v: U64.t) : fx =
  if HeapGraph.is_pointer_field v then begin
    HeapGraph.is_pointer_field_is_obj_addr v;
    let c = resolve_x v f.fh in
    if is_white_x c f.fh then begin
      let f' = { f with fh = makeGray_x c f.fh } in
      if U64.v c < U64.v y then push_fx k f' c else f'
    end else f
  end else f

let rec fix_fields (k: cfg) (y: obj_addr) (j: U64.t{U64.v j >= 1}) (ws: U64.t) (f: fx)
  : Tot fx (decreases (U64.v ws - U64.v j))
  = if U64.v j > U64.v ws then f
    else
      let f' = fix_child k y f (get_field_x f.fh y j) in
      if U64.v j < U64.v ws then fix_fields k y (U64.add j 1UL) ws f' else f'

/// Fix-up steps 3 and 4 at object y.
let fix_obj (k: cfg) (f: fx) (y: obj_addr) : fx =
  if is_gray_x y f.fh then push_fx k f y
  else if is_black_x y f.fh && not (is_no_scan_x y f.fh)
  then fix_fields k y 1UL (wosize_x y f.fh) f
  else f

let rec fix_walk (k: cfg) (f: fx) (l: list obj_addr) : Tot fx (decreases l) =
  match l with
  | [] -> f
  | y :: rest -> fix_walk k (fix_obj k f y) rest

/// The heap's objects, in address order.
let objs_list (h: heap) : list obj_addr = Seq.seq_to_list (objects_x zero_addr h)

let rec any_ovf (ws: list wk) : bool =
  match ws with [] -> false | w :: rest -> w.ovf || any_ovf rest

/// Requirement 5: every overflow[i] and overflow_main.
let flagged (s: state) : bool = s.ovf_main || any_ovf s.wks

let rec all_stopped (ws: list wk) : bool =
  match ws with [] -> true | w :: rest -> Stopped? w.pc && all_stopped rest

let rec clear_ovf (ws: list wk) : list wk =
  match ws with [] -> [] | w :: rest -> { w with ovf = false } :: clear_ovf rest

let rec restart (ws: list wk) : list wk =
  match ws with [] -> [] | w :: rest -> { w with pc = Loop } :: restart rest

let main_step (k: cfg) (s: state) : state =
  if not (flagged s) then { s with finished = true }
  else
    let f = fix_walk k { fh = s.heap; fws = clear_ovf s.wks; fom = false; fn = 0 } (objs_list s.heap) in
    if f.fn = 0 then { s with heap = f.fh; wks = f.fws; ovf_main = f.fom; finished = true }
    else { s with heap = f.fh; wks = restart f.fws; count = f.fn; ovf_main = f.fom }

/// ---------------------------------------------------------------------------
/// Steps and runs
/// ---------------------------------------------------------------------------

let step (k: cfg) (s: state) (e: event) : state =
  if s.finished then s
  else match e with
    | W i -> wstep k s i
    | Main -> if all_stopped s.wks then main_step k s else s

let rec run_from (k: cfg) (s: state) (sched: list event) : Tot state (decreases sched) =
  match sched with
  | [] -> s
  | e :: rest -> run_from k (step k s e) rest

let run (k: cfg) (g: heap) (roots: list obj_addr) (sched: list event) : state =
  run_from k (init k g roots) sched

/// ---------------------------------------------------------------------------
/// The counter
/// ---------------------------------------------------------------------------

/// A worker holds one counted item while it scans, has taken, or has yet
/// to subtract.
let held (p: pc) : nat = match p with Scan _ | Got _ | Finish -> 1 | _ -> 0

/// Every stack entry, inbox entry and held item.
let rec counted (ws: list wk) : nat =
  match ws with
  | [] -> 0
  | w :: rest -> L.length w.stack + L.length w.inbox + held w.pc + counted rest

/// ---------------------------------------------------------------------------
/// What a worker step may read
/// ---------------------------------------------------------------------------

/// The word at a lies in range i.
let in_range (k: cfg) (i: nat) (a: hp_addr) : bool = M1.count_le k.cs (U64.v a) = i

/// The word at a is a field of the object worker i is scanning.
let in_scanned (s: state) (i: nat) (a: hp_addr) : bool =
  match M1.nth s.wks i with
  | Some w ->
    (match w.pc with
     | Scan sc -> U64.v sc.M1.sobj <= U64.v a && U64.v a < U64.v sc.M1.sobj + 8 * U64.v sc.M1.sws
     | _ -> false)
  | None -> false

/// The words worker i's next step may depend on.
let readable (k: cfg) (s: state) (i: nat) (a: hp_addr) : bool = in_range k i a || in_scanned s i a

/// ---------------------------------------------------------------------------
/// Termination
/// ---------------------------------------------------------------------------

/// A worker with nothing to do, while the counter is not 0, spins between
/// Loop and Idle; those steps are not enabled.
let wk_enabled (s: state) (w: wk) : bool =
  match w.pc with
  | Stopped -> false
  | Loop -> Cons? w.stack || Cons? w.inbox || s.count = 0
  | Idle -> Cons? w.inbox || s.count = 0
  | _ -> true

let rec worker_events (s: state) (i: nat) (ws: list wk) : Tot (list event) (decreases ws) =
  match ws with
  | [] -> []
  | w :: rest -> (if wk_enabled s w then [W i] else []) @ worker_events s (i + 1) rest

/// The events that change something.
let enabled (s: state) : list event =
  if s.finished then []
  else worker_events s 0 s.wks @ (if all_stopped s.wks then [Main] else [])

/// An inbox entry, or a taken one, that accept will send on.
let fwd (k: cfg) (h: heap) (v: obj_addr) : bool = own k (resolve_x v h) <> own k v

let entry_w (k: cfg) (h: heap) (v: obj_addr) : nat = if fwd k h v then 7 else 3

let pc_w (k: cfg) (h: heap) (p: pc) : nat =
  match p with
  | Loop -> 2
  | Idle -> 1
  | Stopped -> 0
  | Finish -> 3
  | Got v -> entry_w k h v + 1
  | Scan sc ->
    if U64.v sc.M1.snext <= U64.v sc.M1.sws
    then 9 * (U64.v sc.M1.sws - U64.v sc.M1.snext + 1) + 3 else 3

/// Idle weighs as much as Loop while the counter is not 0, so spinning
/// keeps the measure; one more with a message waiting, so going back to
/// Loop for it lowers the measure.
let idle_w (c: nat) (w: wk) : nat =
  if Idle? w.pc then (if c > 0 then 1 else 0) + (if Cons? w.inbox then 1 else 0) else 0

let rec inbox_w (k: cfg) (h: heap) (l: list obj_addr) : Tot nat (decreases l) =
  match l with [] -> 0 | v :: rest -> entry_w k h v + inbox_w k h rest

let rec wks_w (k: cfg) (h: heap) (c: nat) (ws: list wk) : Tot nat (decreases ws) =
  match ws with
  | [] -> 0
  | w :: rest -> inbox_w k h w.inbox + pc_w k h w.pc + idle_w c w + wks_w k h c rest

let on_stack (k: cfg) (ws: list wk) (x: obj_addr) : bool =
  match M1.nth ws (own k x) with Some w -> L.mem x w.stack | None -> false

/// The work an object still needs: white (2 nr + 3), grey on its owner's
/// stack (2), grey and off it (2 nr + 3); plus 9 per field to scan.
let obj_w (k: cfg) (h: heap) (ws: list wk) (x: obj_addr) : nat =
  let f = 9 * M1.fields_to_scan x h in
  if is_white_x x h then 2 * nr k + 3 + f
  else if is_gray_x x h then (if on_stack k ws x then 2 else 2 * nr k + 3) + f
  else 0

let rec objs_w (k: cfg) (h: heap) (ws: list wk) (l: list obj_addr) : Tot nat (decreases l) =
  match l with [] -> 0 | x :: rest -> obj_w k h ws x + objs_w k h ws rest

/// Every effective step lowers it by at least one (`GC.Spec.MarkPar2`).
let measure (k: cfg) (s: state) : nat =
  objs_w k s.heap s.wks (objs_list s.heap) + wks_w k s.heap s.count s.wks + (if s.finished then 0 else 1)

/// A spin step: worker i, with nothing to do while the counter is not 0,
/// moves between Loop and Idle.
let spin (s: state) (e: event) : bool =
  match e with
  | W i ->
    (match M1.nth s.wks i with
     | Some w -> not s.finished && Nil? w.stack && Nil? w.inbox && s.count > 0 &&
                (Loop? w.pc || Idle? w.pc)
     | None -> false)
  | Main -> false

let rec effective_steps (k: cfg) (s: state) (sched: list event) : Tot nat (decreases sched) =
  match sched with
  | [] -> 0
  | e :: rest -> (if L.mem e (enabled s) then 1 else 0) + effective_steps k (step k s e) rest
