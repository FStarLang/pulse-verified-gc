/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar2.Mutants — deliberately wrong versions of the design
/// (test only)
///
/// Each mutant breaks one rule the design depends on.  The test must catch
/// every one of them, or it cannot see the bugs it is meant to find.
///
///   1 no_main_flag   the overflow check after a round ignores
///                    overflow_main: a root left grey by a full stack at
///                    setup is never scanned.
///   2 infix_root     setup greys an infix root's own header word instead of
///                    resolving it to its closure.
///   3 sender_resolves  route resolves an infix pointer itself, reading the
///                    header word at v - 8, which another worker may own
///                    (the Stage 1 model's routing).  Colours stay right; the
///                    read breaks the ownership rule.
///   4 silent_drop    a full inbox drops the message without setting the
///                    sender's flag.
///   5 early_subtract a worker subtracts 1 as soon as it pops or takes an
///                    item, before adding the work that item creates.
///
/// Mutant 0 is the model itself, written again here; the test checks it
/// agrees with `GC.Spec.MarkPar2.Model.step` and `init`.
/// ---------------------------------------------------------------------------
module GC.Spec.MarkPar2.Mutants

open FStar.Seq
module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot
open FStar.List.Tot { (@) }

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.MarkPar.Exec
open GC.Spec.MarkPar2.Model

module HeapGraph = GC.Spec.HeapGraph
module M1 = GC.Spec.MarkPar.Model

let send_m (m: nat) (k: cfg) (s: state) (me j: nat) (v: obj_addr) : state =
  match M1.nth s.wks j with
  | Some wj ->
    if L.length wj.inbox >= k.cap_q then (if m = 4 then s else set_ovf s me)
    else { s with wks = M1.set_nth s.wks j { wj with inbox = wj.inbox @ [v] };
                  count = s.count + 1 }
  | None -> s

let accept_m (m: nat) (k: cfg) (s: state) (me: nat) (v: obj_addr) : state =
  let c = resolve_x v s.heap in
  let o = own k c in
  if o <> me then send_m m k s me o c else grey_push k s me c

let route_m (m: nat) (k: cfg) (s: state) (me: nat) (v: obj_addr) : state =
  if m = 3 then begin
    let c = resolve_x v s.heap in
    let o = own k c in
    if o = me then grey_push k s me c else send_m m k s me o c
  end else begin
    let o = own k v in
    if o = me then accept_m m k s me v else send_m m k s me o v
  end

let dec (m: nat) (n: nat) : nat = if m = 5 then (if n > 0 then n - 1 else 0) else n

let wstep_m (m: nat) (k: cfg) (s: state) (i: nat) : state =
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
         { s with heap = makeBlack_x x s.heap; count = dec m s.count;
                  wks = M1.set_nth s.wks i { w with stack = rest; pc = pc' } }
       | [] ->
         (match w.inbox with
          | v :: rest -> { s with count = dec m s.count;
                                  wks = M1.set_nth s.wks i { w with inbox = rest; pc = Got v } }
          | [] ->
            if s.count = 0 then { s with wks = M1.set_nth s.wks i { w with pc = Stopped } }
            else s))
    | Scan sc ->
      let pc' = match M1.next_field sc with Some sc' -> Scan sc' | None -> Finish in
      let s0 = { s with wks = M1.set_nth s.wks i { w with pc = pc' } } in
      let v = get_field_x s.heap sc.M1.sobj sc.M1.snext in
      if HeapGraph.is_pointer_field v then begin
        HeapGraph.is_pointer_field_is_obj_addr v;
        route_m m k s0 i v
      end else s0
    | Got v -> accept_m m k { s with wks = M1.set_nth s.wks i { w with pc = Finish } } i v
    | Finish ->
      { s with wks = M1.set_nth s.wks i { w with pc = Loop };
               count = if m = 5 then s.count else (if s.count > 0 then s.count - 1 else 0) }
    | Stopped -> s

let darken_m (m: nat) (k: cfg) (f: fx) (r: obj_addr) : fx =
  let c = if m = 2 then r else resolve_x r f.fh in
  if is_white_x c f.fh then push_fx k { f with fh = makeGray_x c f.fh } c else f

let rec setup_m (m: nat) (k: cfg) (f: fx) (roots: list obj_addr) : Tot fx (decreases roots) =
  match roots with
  | [] -> f
  | r :: rest -> setup_m m k (darken_m m k f r) rest

let init_m (m: nat) (k: cfg) (g: heap) (roots: list obj_addr) : state =
  let f = setup_m m k { fh = g; fws = blanks (nr k); fom = false; fn = 0 } roots in
  { heap = f.fh; wks = f.fws; count = f.fn; ovf_main = f.fom; finished = false }

let flagged_m (m: nat) (s: state) : bool = (if m = 1 then false else s.ovf_main) || any_ovf s.wks

let main_step_m (m: nat) (k: cfg) (s: state) : state =
  if not (flagged_m m s) then { s with finished = true }
  else
    let f = fix_walk k { fh = s.heap; fws = clear_ovf s.wks; fom = false; fn = 0 } (objs_list s.heap) in
    if f.fn = 0 then { s with heap = f.fh; wks = f.fws; ovf_main = f.fom; finished = true }
    else { s with heap = f.fh; wks = restart f.fws; count = f.fn; ovf_main = f.fom }

let step_m (m: nat) (k: cfg) (s: state) (e: event) : state =
  if s.finished then s
  else match e with
    | W i -> wstep_m m k s i
    | Main -> if all_stopped s.wks then main_step_m m k s else s
