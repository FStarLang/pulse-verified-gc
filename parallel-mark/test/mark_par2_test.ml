(* Stage 3 test: run the extracted model of docs/parallel-mark-design.md,
   GC.Spec.MarkPar2.Model, under random interleavings and random stack and
   inbox capacities, and compare it with the extracted
   GC.Spec.MarkPar.Model.sequential_mark_x.

     mark_par2_test hand              hand-built cases
     mark_par2_test random SEED N     N generated heaps

   At every step of the model it also checks:
     writes   every byte a worker step changes lies in the header of an
              enumerated object the worker owns; Main runs only when every
              worker has stopped
     reads    the step gives the same result on a heap where every word it
              may not read (GC.Spec.MarkPar2.Model.readable) is scrambled
     counter  count equals the counted entries; a worker step from count 0
              leaves it 0
     measure  an enabled step lowers it; a step that is not enabled changes
              nothing, or is a spin step (Loop <-> Idle with nothing to do
              while count > 0) that keeps it and that the worker's next
              step undoes; nothing is enabled exactly when marking is done.
   The scheduler takes spin steps too, so a worker can sit in Idle, between
   finding its inbox empty and reading the counter, while a message
   arrives.
   The heap size is fixed per process (PS_WORDS, see GC_Spec_ZeroAddr.ml).
   The first failure of the model stops the run with exit 1.  The mutants
   (GC.Spec.MarkPar2.Mutants) run on the same cases; "mutant M caught C of
   R" is printed for each. *)

module U64 = Stdint.Uint64
module Seq = FStar_Seq_Base
module H = GC_Lib_Header
module M1 = GC_Spec_MarkPar_Model
module MP = GC_Spec_MarkPar2_Model
module MU = GC_Spec_MarkPar2_Mutants
module X = GC_Spec_MarkPar_Exec

let zero = U64.to_int GC_Spec_Base.zero_addr
let hsize = Z.to_int GC_Spec_Base.heap_size
let words = (hsize - zero) / 8

let rint n = if n <= 0 then 0 else Random.int n
let pick a = a.(rint (Array.length a))
let pickl l = List.nth l (rint (List.length l))

(* ------------------------------------------------------------------ *)
(* Heaps, described by object index                                    *)
(* ------------------------------------------------------------------ *)

type fv =
  | Int of U64.t          (* a raw word *)
  | Ptr of int            (* the address of object j *)
  | Inf of int * int      (* the address of the infix object at field i of closure j *)
  | Hdr of int            (* an infix header at this field, offset i *)

type ob = { wz : int; color : H.color_sem; tag : int; fields : fv array }

let color_name = function H.White -> "W" | H.Gray -> "G" | H.Blue -> "U" | H.Black -> "B"

let hdrs (objs : ob array) =
  let a = Array.make (Array.length objs) 0 in
  let p = ref zero in
  Array.iteri (fun j o -> a.(j) <- !p; p := !p + 8 * (o.wz + 1)) objs;
  a

let write_bytes (b : int array) a (v : U64.t) =
  for k = 0 to 7 do
    b.(a + k) <- U64.to_int (U64.logand (U64.shift_right v (8 * k)) (U64.of_int 255))
  done

let word_of hd = function
  | Int v -> v
  | Ptr j -> U64.of_int (hd.(j) + 8)
  | Inf (j, i) -> U64.of_int (hd.(j) + 8 + 8 * i)
  | Hdr i -> GC_Spec_Object.makeHeader (U64.of_int i) H.White (U64.of_int 249)

let build (objs : ob array) : GC_Spec_Base.heap =
  let total = Array.fold_left (fun s o -> s + o.wz + 1) 0 objs in
  if total <> words then failwith (Printf.sprintf "build: %d words, heap has %d" total words);
  let b = Array.make hsize 0 in
  let hd = hdrs objs in
  Array.iteri (fun j o ->
      write_bytes b hd.(j) (GC_Spec_Object.makeHeader (U64.of_int o.wz) o.color (U64.of_int o.tag));
      Array.iteri (fun i v -> write_bytes b (hd.(j) + 8 * (i + 1)) (word_of hd v)) o.fields)
    objs;
  let g = Seq.seq_of_list (Array.to_list b) in
  Array.iteri (fun j o ->
      let h = GC_Spec_Heap.read_word g (U64.of_int hd.(j)) in
      if U64.to_int (GC_Spec_Object.getWosize h) <> o.wz
         || GC_Spec_Object.getColor h <> o.color then failwith "build: header mismatch")
    objs;
  g

(* ------------------------------------------------------------------ *)
(* Reading a heap back, independently of the model                     *)
(* ------------------------------------------------------------------ *)

let rw g a = GC_Spec_Heap.read_word g (U64.of_int a)
let wz_at g x = U64.to_int (GC_Spec_Object.getWosize (rw g (x - 8)))
let tag_at g x = U64.to_int (GC_Spec_Object.getTag (rw g (x - 8)))
let col_at g x = GC_Spec_Object.getColor (rw g (x - 8))

let objects g =
  List.map U64.to_int (Seq.seq_to_list (X.objects_x GC_Spec_Base.zero_addr g))

let is_ptr v =
  let n = U64.to_int v in
  U64.compare v (U64.of_int hsize) < 0 && n mod 8 = 0 && n >= zero + 8

(* resolve_object, written out again from its specification *)
let resolve g v =
  if tag_at g v = 249 then
    let p = v - 8 * wz_at g v in
    if p >= 8 && p < hsize && p mod 8 = 0 then p else v
  else v

let scannable g x = tag_at g x < 251 && col_at g x <> H.Blue

let fields g x = List.init (wz_at g x) (fun i -> rw g (x + 8 * i))

(* well_formed_heap parts 1-4, no grey or black object, no pointer to blue,
   each root names (after resolving) an enumerated white object.  Roots may
   be infix pointers and may repeat. *)
let pre_ok g roots =
  let objs = objects g in
  let set = Hashtbl.create 64 in
  List.iter (fun o -> Hashtbl.replace set o ()) objs;
  let mem x = Hashtbl.mem set x in
  let ok = ref (objs <> []) in
  let bad why = if !ok then Printf.printf "pre: %s\n" why; ok := false in
  List.iter (fun o ->
      if o + 8 * wz_at g o > hsize then bad "part 1";
      if tag_at g o = 249 then bad "part 4";
      (match col_at g o with H.White | H.Blue -> () | _ -> bad "grey or black");
      if scannable g o then
        List.iter (fun v ->
            if is_ptr v then begin
              let d = U64.to_int v in
              let r = resolve g d in
              if not (mem r) then bad "part 2";
              if mem r && col_at g r = H.Blue then bad "pointer to blue";
              if tag_at g d = 249 then begin
                let w = wz_at g d in
                if not (w >= 2 && mem r && tag_at g r = 247 && d < r + 8 * wz_at g r) then bad "part 3"
              end
            end)
          (fields g o))
    objs;
  List.iter (fun r ->
      let c = resolve g r in
      if not (mem c) || col_at g c <> H.White then bad "root") roots;
  !ok

(* Reachability from the roots, by a plain search. *)
let reach g roots =
  let seen = Hashtbl.create 64 in
  let rec go = function
    | [] -> ()
    | x :: rest ->
      if Hashtbl.mem seen x then go rest
      else begin
        Hashtbl.replace seen x ();
        let kids =
          if scannable g x then
            List.filter_map (fun v -> if is_ptr v then Some (resolve g (U64.to_int v)) else None)
              (fields g x)
          else [] in
        go (kids @ rest)
      end in
  go (List.map (resolve g) roots);
  seen

(* ------------------------------------------------------------------ *)
(* Statistics                                                          *)
(* ------------------------------------------------------------------ *)

let nmut = 6

type stats = {
  mutable heaps : int; mutable cutsets : int; mutable runs : int; mutable events : int;
  mutable runs_k : int array;          (* by k = 1, 2, 4, 8, other *)
  mutable sent : int;                  (* appends to another worker's inbox *)
  mutable dropped : int;               (* sends to a full inbox *)
  mutable stack_full : int;            (* greys left off a full stack, in a round *)
  mutable setup_full : int;            (* runs whose setup filled a stack *)
  mutable fixups : int;                (* fix-ups that started another round *)
  mutable max_rounds : int;            (* most rounds in one run *)
  mutable forwards : int;              (* accepts that sent a closure on *)
  mutable zero_reads : int;            (* worker steps taken at count 0 *)
  mutable scrambles : int;             (* read checks done *)
  mutable infix_split : int;
  mutable black : int; mutable white_left : int;
  mutable rejected : int;
  mutable idle_tried : int;
  mutable spins : int;                 (* spin steps taken *)
  mutable late_msgs : int;             (* Idle steps that found a message come in *)
  mutable idle_stops : int;            (* Idle steps that read 0 and stopped *)
  mutable max_ratio : float;
  mutable infix_roots : int; mutable repeat_roots : int;
  mut_runs : int array; mut_caught : int array;
  mut_by_heap : int array; mut_by_write : int array; mut_by_read : int array;
  mut_by_stuck : int array; mut_by_count : int array;
}

let st = { heaps = 0; cutsets = 0; runs = 0; events = 0; runs_k = Array.make 5 0;
           sent = 0; dropped = 0; stack_full = 0; setup_full = 0; fixups = 0; max_rounds = 0;
           forwards = 0; zero_reads = 0; scrambles = 0; infix_split = 0;
           black = 0; white_left = 0; rejected = 0; idle_tried = 0; spins = 0; late_msgs = 0; idle_stops = 0; max_ratio = 0.;
           infix_roots = 0; repeat_roots = 0;
           mut_runs = Array.make (nmut + 1) 0; mut_caught = Array.make (nmut + 1) 0;
           mut_by_heap = Array.make (nmut + 1) 0; mut_by_write = Array.make (nmut + 1) 0;
           mut_by_read = Array.make (nmut + 1) 0; mut_by_stuck = Array.make (nmut + 1) 0;
           mut_by_count = Array.make (nmut + 1) 0 }

let kslot k = match k with 1 -> 0 | 2 -> 1 | 4 -> 2 | 8 -> 3 | _ -> 4

(* ------------------------------------------------------------------ *)
(* Describing a failure                                                *)
(* ------------------------------------------------------------------ *)

let zl = List.map Z.of_int
let owner cs x = Z.to_int (M1.owner (zl cs) (U64.of_int x))

let describe g cs roots =
  let b = Buffer.create 256 in
  Buffer.add_string b (Printf.sprintf "heap: zero_addr=%d heap_size=%d (%d words)\n" zero hsize words);
  Buffer.add_string b (Printf.sprintf "cuts: [%s]\n" (String.concat "; " (List.map string_of_int cs)));
  Buffer.add_string b (Printf.sprintf "roots: [%s]\n" (String.concat "; " (List.map string_of_int roots)));
  List.iter (fun o ->
      Buffer.add_string b (Printf.sprintf "  obj %d (hdr @%d, range %d): wz=%d %s tag=%d  fields [%s]\n"
        o (o - 8) (owner cs o) (wz_at g o) (color_name (col_at g o)) (tag_at g o)
        (String.concat " " (List.map U64.to_string (fields g o)))))
    (objects g);
  Buffer.contents b

let ev_name = function
  | MP.W i -> Printf.sprintf "W %s" (Z.to_string i)
  | MP.Main -> "Main"

let first_diff (a : int list) (b : int list) =
  let rec go i = function
    | x :: xs, y :: ys -> if x <> y then Some i else go (i + 1) (xs, ys)
    | _ -> None in
  go 0 (a, b)

let bytes (h : GC_Spec_Base.heap) : int list = Seq.seq_to_list h

let fail what g (k : MP.cfg) cs roots sched (hs : GC_Spec_Base.heap) (hp : GC_Spec_Base.heap) =
  Printf.printf "FAILURE: %s\n" what;
  Printf.printf "S=%s Q=%s\n" (Z.to_string k.MP.cap_s) (Z.to_string k.MP.cap_q);
  print_string (describe g cs roots);
  Printf.printf "schedule (%d events): %s\n" (List.length sched)
    (String.concat ", " (List.map ev_name sched));
  (match first_diff (bytes hs) (bytes hp) with
   | None -> print_string "heaps equal\n"
   | Some i ->
     let a = i land (lnot 7) in
     Printf.printf "heaps differ first in the word @%d: expected %s, got %s\n"
       a (U64.to_string (rw hs a)) (U64.to_string (rw hp a)));
  exit 1

(* ------------------------------------------------------------------ *)
(* Checks on one step                                                  *)
(* ------------------------------------------------------------------ *)

(* The heap as an array of words, read once. *)
let words_of (h : GC_Spec_Base.heap) : U64.t array =
  let b = Array.of_list (Seq.seq_to_list h) in
  Array.init (hsize / 8) (fun j ->
      let v = ref U64.zero in
      for q = 7 downto 0 do
        v := U64.logor (U64.shift_left !v 8) (U64.of_int b.(8 * j + q))
      done;
      !v)

(* Every word a worker step changed is the header of an enumerated object
   the worker owns. *)
let writes_ok objset cs i (w0 : U64.t array) (w1 : U64.t array) =
  let ok = ref true in
  Array.iteri (fun j v ->
      if v <> w1.(j) then begin
        let o = 8 * j + 8 in
        if not (Hashtbl.mem objset o) || owner cs o <> i then ok := false
      end)
    w0;
  !ok

let heap_of_words (ws : U64.t array) : GC_Spec_Base.heap =
  let b = Array.make hsize 0 in
  Array.iteri (fun j v -> write_bytes b (8 * j) v) ws;
  Seq.seq_of_list (Array.to_list b)

(* A heap equal to h on every word worker i may read, and different
   elsewhere: random words, or infix-looking headers with a random offset,
   or zeros. *)
let scramble k s i (w : U64.t array) =
  let mode = rint 3 in
  Array.mapi (fun j v ->
      if MP.readable k s (Z.of_int i) (U64.of_int (8 * j)) then v
      else match mode with
        | 0 -> U64.logxor v (U64.of_int64 (Random.int64 Int64.max_int))
        | 1 -> GC_Spec_Object.makeHeader (U64.of_int (1 + rint 6)) (pick [| H.White; H.Gray; H.Black |]) (U64.of_int 249)
        | _ -> U64.zero)
    w

(* The step on the scrambled heap: same workers, counter and flags, and
   every word either step writes, both write with the same value. *)
let reads_ok step k s i (w : U64.t array) (wa : U64.t array) =
  let w2 = scramble k s i w in
  let s2 = { s with MP.heap = heap_of_words w2 } in
  let e = MP.W (Z.of_int i) in
  let a = step s e and b = step s2 e in
  st.scrambles <- st.scrambles + 1;
  a.MP.wks = b.MP.wks && a.MP.count = b.MP.count && a.MP.ovf_main = b.MP.ovf_main
  && a.MP.finished = b.MP.finished
  && (let wb = words_of b.MP.heap in
      let ok = ref true in
      Array.iteri (fun j v ->
          if (wa.(j) <> v || wb.(j) <> w2.(j)) && wa.(j) <> wb.(j) then ok := false)
        w;
      !ok)

let counted s = Z.to_int (MP.counted s.MP.wks)

(* ------------------------------------------------------------------ *)
(* Schedulers                                                          *)
(* ------------------------------------------------------------------ *)

let nstrategies = 4
let strategy_name = [| "uniform"; "one worker"; "round robin"; "slow worker" |]

let actor = function MP.W i -> Z.to_int i | MP.Main -> -1

let choose strat cur slow (en : MP.event list) =
  match strat with
  | 0 -> pickl en
  | 1 ->
    let mine = List.filter (fun e -> actor e = !cur) en in
    if mine <> [] && rint 10 < 9 then pickl mine
    else (let e = pickl en in cur := actor e; e)
  | 2 ->
    let ws = List.sort_uniq compare (List.map actor en) in
    let next = match List.filter (fun w -> w >= !cur) ws with w :: _ -> w | [] -> List.hd ws in
    cur := next + 1;
    List.find (fun e -> actor e = next) en
  | _ ->
    (* one worker moves only when nothing else can *)
    let others = List.filter (fun e -> actor e <> slow) en in
    if others <> [] && rint 20 > 0 then pickl others else pickl en

(* ------------------------------------------------------------------ *)
(* One run                                                             *)
(* ------------------------------------------------------------------ *)

let limit = 400000

type outcome = { heap : GC_Spec_Base.heap; finished : bool; writes : bool; reads : bool;
                 cnt : bool; sched : MP.event list }

(* Run mutant m (0 = the model) under strategy strat until it is done, or
   no event is enabled, or the step limit. *)
let run_one m strat k cs g roots objset =
  let r64 = List.map U64.of_int roots in
  let zm = Z.of_int m in
  let s = ref (if m = 0 then MP.init k g r64 else MU.init_m zm k g r64) in
  if m = 0 && (MU.init_m zm k g r64) <> !s then fail "init_m 0 differs from init" g k cs roots [] g g;
  if m = 0 && !s.MP.ovf_main then st.setup_full <- st.setup_full + 1;
  let step = if m = 0 then MP.step k else MU.step_m zm k in
  let sched = ref [] in
  let steps = ref 0 in
  let spins = ref 0 in
  let nw = List.length cs + 1 in
  let wr = ref true and rd = ref true and cn = ref true in
  let cur = ref 0 in
  let slow = rint (List.length cs + 1) in
  let rounds = ref 1 in
  let stuck = ref false in
  let fl why s' e =
    fail why g k cs roots (List.rev (e :: !sched)) !s.MP.heap s'.MP.heap in
  while not !s.MP.finished && not !stuck do
    let en = MP.enabled !s in
    if en = [] then begin
      if m = 0 then fail "nothing enabled, but marking is not done" g k cs roots (List.rev !sched) g !s.MP.heap;
      stuck := true
    end else begin
      let sp = List.filter (fun e -> MP.spin !s e) (List.init nw (fun i -> MP.W (Z.of_int i))) in
      let e = if sp <> [] && rint 3 = 0 then pickl sp else choose strat cur slow en in
      let is_spin = not (List.mem e en) in
      let s' = step !s e in
      (* writes; Main only at the stop barrier *)
      (match e with
       | MP.W i ->
         let w0 = words_of !s.MP.heap and w1 = words_of s'.MP.heap in
         if not (writes_ok objset cs (Z.to_int i) w0 w1) then begin
           wr := false; if m = 0 then fl "a worker wrote outside its own objects' headers" s' e end;
         if rint 2 = 0 || m <> 0 then
           if not (reads_ok step k !s (Z.to_int i) w0 w1) then begin
             rd := false; if m = 0 then fl "a worker step read a word it may not" s' e end;
         if !s.MP.count = Z.zero then begin
           st.zero_reads <- st.zero_reads + 1;
           if s'.MP.count <> Z.zero then begin
             cn := false; if m = 0 then fl "count left 0 inside a round" s' e end
         end
       | MP.Main ->
         if not (MP.all_stopped !s.MP.wks) then fl "Main ran before every worker stopped" s' e;
         if not s'.MP.finished then begin incr rounds; if m = 0 then st.fixups <- st.fixups + 1 end);
      if counted s' <> Z.to_int s'.MP.count then begin
        cn := false; if m = 0 then fl "count differs from the counted entries" s' e end;
      if m = 0 then begin
        let ms = Z.to_int (MP.measure k !s) and ms' = Z.to_int (MP.measure k s') in
        if is_spin then begin
          if ms' <> ms then fl (Printf.sprintf "spin %s changed the measure (%d -> %d)" (ev_name e) ms ms') s' e;
          if step s' e <> !s then fl (Printf.sprintf "spin %s was not undone by the next step" (ev_name e)) s' e
        end else if ms' >= ms then fl (Printf.sprintf "%s did not lower the measure (%d -> %d)" (ev_name e) ms ms') s' e;
        if rint 8 = 0 then begin
          let d = if rint 4 = 0 then MP.Main else MP.W (Z.of_int (rint (List.length cs + 2))) in
          if not (List.mem d en) then begin
            st.idle_tried <- st.idle_tried + 1;
            let t = MP.step k !s d in
            if t <> !s && not (MP.spin !s d && MP.measure k t = MP.measure k !s && MP.step k t d = !s) then
              fl (Printf.sprintf "%s is not enabled, changed the state, and is not a spin" (ev_name d)) s' e
          end
        end;
        if MU.step_m zm k !s e <> s' then fl "step_m 0 differs from step" s' e;
        (* coverage *)
        let ovfs t = List.length (List.filter (fun w -> w.MP.ovf) t.MP.wks) in
        let inb t = List.fold_left (fun a w -> a + List.length w.MP.inbox) 0 t.MP.wks in
        (match e with
         | MP.W i ->
           let w = List.nth !s.MP.wks (Z.to_int i) in
           let fresh = ovfs s' > ovfs !s in
           let sends = inb s' > inb !s in
           if sends then st.sent <- st.sent + 1;
           if fresh then begin
             let pushes = List.length (List.nth s'.MP.wks (Z.to_int i)).MP.stack in
             if pushes >= Z.to_int k.MP.cap_s && s'.MP.heap <> !s.MP.heap then st.stack_full <- st.stack_full + 1
             else st.dropped <- st.dropped + 1
           end;
           (match w.MP.pc with
            | MP.Got v -> if MP.fwd k !s.MP.heap v then st.forwards <- st.forwards + 1
            | MP.Idle ->
              if !s.MP.count = Z.zero then st.idle_stops <- st.idle_stops + 1
              else if w.MP.inbox <> [] then st.late_msgs <- st.late_msgs + 1
            | _ -> ())
         | MP.Main -> ())
      end;
      s := s';
      sched := e :: !sched;
      if is_spin then (incr spins; if m = 0 then st.spins <- st.spins + 1) else incr steps;
      if !steps + !spins > limit then begin
        if m = 0 then fail "no end after the step limit" g k cs roots [] g !s.MP.heap;
        stuck := true
      end
    end
  done;
  if m = 0 then begin
    if MP.enabled !s <> [] then fail "done, but an event is enabled" g k cs roots (List.rev !sched) g !s.MP.heap;
    let m0 = Z.to_int (MP.measure k (MP.init k g r64)) in
    if !steps > m0 then fail "more effective steps than the initial measure" g k cs roots (List.rev !sched) g !s.MP.heap;
    if MP.effective_steps k (MP.init k g r64) (List.rev !sched) <> Z.of_int !steps then
      fail "effective_steps miscounts" g k cs roots (List.rev !sched) g !s.MP.heap;
    st.max_ratio <- max st.max_ratio (float !steps /. float (max 1 m0));
    st.events <- st.events + !steps;
    st.max_rounds <- max st.max_rounds !rounds
  end;
  { heap = !s.MP.heap; finished = !s.MP.finished; writes = !wr; reads = !rd; cnt = !cn;
    sched = List.rev !sched }

(* ------------------------------------------------------------------ *)
(* One heap                                                            *)
(* ------------------------------------------------------------------ *)

let check_reference g roots (hs : GC_Spec_Base.heap) =
  let r = reach g roots in
  let objs = objects g in
  let hdr_of = Hashtbl.create 64 in
  let k0 = { MP.cs = []; MP.cap_s = Z.one; MP.cap_q = Z.zero } in
  List.iter (fun x ->
      let b = X.is_black_x (U64.of_int x) hs in
      if b <> Hashtbl.mem r x then fail "reference: black is not reachable" g k0 [] roots [] g hs;
      if b then begin
        st.black <- st.black + 1;
        Hashtbl.replace hdr_of (x - 8) ();
        if rw hs (x - 8) <> rw (X.makeBlack_x (U64.of_int x) g) (x - 8) then
          fail "reference: header is not the original made black" g k0 [] roots [] g hs
      end else if col_at g x = H.White then st.white_left <- st.white_left + 1)
    objs;
  let a = ref 0 in
  while !a < hsize do
    if not (Hashtbl.mem hdr_of !a) && rw hs !a <> rw g !a then
      fail (Printf.sprintf "reference: word @%d changed" !a) g k0 [] roots [] g hs;
    a := !a + 8
  done

let check_rejects () =
  let bad = [ [zero]; [hsize]; [zero + 9; zero + 9]; [zero + 17; zero + 9]; [hsize + 3] ] in
  List.iter (fun cs ->
      if MP.valid_cfg { MP.cs = zl cs; MP.cap_s = Z.one; MP.cap_q = Z.one } then begin
        Printf.printf "valid_cfg accepted [%s]\n" (String.concat "; " (List.map string_of_int cs));
        exit 1
      end;
      st.rejected <- st.rejected + 1)
    bad;
  if MP.valid_cfg { MP.cs = []; MP.cap_s = Z.zero; MP.cap_q = Z.one } then begin
    print_endline "valid_cfg accepted S = 0"; exit 1 end;
  st.rejected <- st.rejected + 1

let gen_cuts g k infixes =
  let objs = Array.of_list (objects g) in
  let one () =
    match rint 4 with
    | 0 -> zero + 1 + rint (hsize - zero - 1)
    | 1 -> let o = pick objs in o - 8
    | 2 -> let o = pick objs in o - 8 + 1 + rint 8
    | _ ->
      if infixes = [] then zero + 1 + rint (hsize - zero - 1)
      else let (c, d) = pickl infixes in (c - 8) + 1 + rint (d - c)
  in
  let rec go acc =
    if List.length acc >= k - 1 then List.sort compare acc
    else
      let c = one () in
      if c > zero && c < hsize && not (List.mem c acc) then go (c :: acc) else go acc in
  go []

let infix_pairs g =
  List.concat_map (fun o ->
      if tag_at g o = 247 then
        List.filter_map (fun (i, v) ->
            if U64.to_int (GC_Spec_Object.getTag v) = 249 then Some (o, o + 8 * i) else None)
          (List.mapi (fun i v -> (i + 1, v)) (fields g o))
      else [])
    (objects g)

let caps () =
  let s = pick [| 1; 1; 1; 2; 3; 1000 |] and q = pick [| 0; 1; 1; 2; 4; 1000 |] in
  (Z.of_int s, Z.of_int q)

let run_case g cs roots ~model_runs ~mutant_runs =
  let k = List.length cs + 1 in
  st.cutsets <- st.cutsets + 1;
  let objset = Hashtbl.create 64 in
  List.iter (fun o -> Hashtbl.replace objset o ()) (objects g);
  let r = reach g roots in
  if List.exists (fun (c, d) -> Hashtbl.mem r c && owner cs d <> owner cs c) (infix_pairs g) then
    st.infix_split <- st.infix_split + 1;
  let hs = M1.sequential_mark_x g (List.map U64.of_int roots) in
  for n = 0 to model_runs - 1 do
    let (s, q) = caps () in
    let cfg = { MP.cs = zl cs; MP.cap_s = s; MP.cap_q = q } in
    if not (MP.valid_cfg cfg) then fail "valid_cfg rejected a generated configuration" g cfg cs roots [] g g;
    let strat = n mod nstrategies in
    let o = run_one 0 strat cfg cs g roots objset in
    st.runs <- st.runs + 1;
    st.runs_k.(kslot k) <- st.runs_k.(kslot k) + 1;
    if bytes o.heap <> bytes hs then
      fail (Printf.sprintf "parallel heap differs from the sequential mark (%s)" strategy_name.(strat))
        g cfg cs roots o.sched hs o.heap;
    let fin = MP.run cfg g (List.map U64.of_int roots) o.sched in
    if not fin.MP.finished || bytes fin.MP.heap <> bytes o.heap then
      fail "replaying the schedule through run differs" g cfg cs roots o.sched o.heap fin.MP.heap
  done;
  for m = 1 to nmut do
    for n = 0 to mutant_runs - 1 do
      let (s, q) = caps () in
      let cfg = { MP.cs = zl cs; MP.cap_s = s; MP.cap_q = q } in
      let strat = n mod nstrategies in
      let o = run_one m strat cfg cs g roots objset in
      st.mut_runs.(m) <- st.mut_runs.(m) + 1;
      let by_heap = o.finished && bytes o.heap <> bytes hs in
      let by_stuck = not o.finished in
      if by_heap then st.mut_by_heap.(m) <- st.mut_by_heap.(m) + 1;
      if by_stuck then st.mut_by_stuck.(m) <- st.mut_by_stuck.(m) + 1;
      if not o.writes then st.mut_by_write.(m) <- st.mut_by_write.(m) + 1;
      if not o.reads then st.mut_by_read.(m) <- st.mut_by_read.(m) + 1;
      if not o.cnt then st.mut_by_count.(m) <- st.mut_by_count.(m) + 1;
      if by_heap || by_stuck || not o.writes || not o.reads || not o.cnt then
        st.mut_caught.(m) <- st.mut_caught.(m) + 1
    done
  done

let run_heap objs roots ~cutsets ~model_runs ~mutant_runs ~extra_cuts =
  let g = build objs in
  let hd = hdrs objs in
  let roots = List.map (fun f -> U64.to_int (word_of hd f)) roots in
  if List.exists (fun r -> tag_at g r = 249) roots then st.infix_roots <- st.infix_roots + 1;
  if List.length (List.sort_uniq compare (List.map (resolve g) roots)) < List.length roots then
    st.repeat_roots <- st.repeat_roots + 1;
  if not (pre_ok g roots) then begin
    print_string (describe g [] roots); failwith "generated heap fails the precondition"
  end;
  st.heaps <- st.heaps + 1;
  check_reference g roots (M1.sequential_mark_x g (List.map U64.of_int roots));
  let infixes = infix_pairs g in
  List.iter (fun cs -> run_case g cs roots ~model_runs ~mutant_runs) (extra_cuts hd);
  List.iter (fun k ->
      for _ = 1 to (if k = 1 then 1 else cutsets) do
        run_case g (gen_cuts g k infixes) roots ~model_runs ~mutant_runs
      done)
    [1; 2; 4; 8]

(* ------------------------------------------------------------------ *)
(* Generated heaps                                                     *)
(* ------------------------------------------------------------------ *)

let rand_word () =
  match rint 6 with
  | 0 -> U64.zero
  | 1 -> U64.of_int (2 * rint 1000 + 1)                     (* an OCaml int *)
  | 2 -> U64.of_int (8 * rint (zero / 8))                   (* aligned, below the heap *)
  | 3 -> U64.of_int (hsize + 8 * rint 100)                  (* aligned, above the heap *)
  | 4 -> U64.of_int (zero + 8 + 8 * rint words + 1 + rint 7) (* in range, not aligned *)
  | _ -> U64.of_int64 (Random.int64 Int64.max_int)

let gen_heap () =
  let p_blue = pick [| 0.; 0.1; 0.3 |] in
  let p_ptr = pick [| 0.2; 0.5; 0.8; 1.0 |] in
  let objs = ref [] in
  let rem = ref words in
  while !rem > 0 do
    let r = !rem in
    let kind = rint 10 in
    let size, tag, infix =
      if kind < 2 && r >= 5 then begin
        (* a closure, with one or two infix headers at fields 2 .. wz-1 *)
        let wz = 4 + rint (min 6 (r - 5) + 1) in
        let wz = if r - (wz + 1) = 1 then wz + 1 else wz in
        let a = 2 + rint (wz - 2) in
        let b = 2 + rint (wz - 2) in
        (wz + 1, 247, List.sort_uniq compare (if rint 2 = 0 then [a] else [a; b]))
      end else begin
        let wz = if kind = 2 then rint 4 else pick [| 0; 0; 1; 1; 1; 2; 2; 3; 4; 6 |] in
        let s = min (wz + 1) r in
        let s = if r - s = 1 then s + 1 else s in
        (s, (if kind = 2 then 252 else pick [| 0; 0; 1; 2 |]), [])
      end in
    let wz = size - 1 in
    let color = if Random.float 1. < p_blue then H.Blue else H.White in
    let fields = Array.init wz (fun i -> if List.mem (i + 1) infix then Hdr (i + 1) else Int U64.zero) in
    objs := { wz; color; tag; fields } :: !objs;
    rem := r - size
  done;
  let objs = Array.of_list (List.rev !objs) in
  let n = Array.length objs in
  let live = List.filter (fun j -> objs.(j).color = H.White) (List.init n Fun.id) in
  let infix_targets =
    List.concat_map (fun j ->
        if objs.(j).tag = 247 && objs.(j).color = H.White then
          List.filter_map (fun (i, f) -> match f with Hdr _ -> Some (j, i) | _ -> None)
            (List.mapi (fun i f -> (i + 1, f)) (Array.to_list objs.(j).fields))
        else [])
      live in
  Array.iter (fun o ->
      let scan = o.tag < 251 && o.color = H.White in
      Array.iteri (fun i f ->
          match f with
          | Hdr _ -> ()
          | _ ->
            o.fields.(i) <-
              if scan then begin
                if live <> [] && Random.float 1. < p_ptr then
                  (if infix_targets <> [] && rint 4 = 0 then (let (j, k) = pickl infix_targets in Inf (j, k))
                   else Ptr (pickl live))
                else Int (rand_word ())
              end else
                (* no-scan bodies and free blocks: anything, including
                   addresses of objects, live or free *)
                (if rint 2 = 0 then Ptr (rint n) else Int (rand_word ())))
        o.fields)
    objs;
  let roots =
    if live = [] || rint 20 = 0 then []
    else begin
      let sh = List.map snd (List.sort compare (List.map (fun j -> (Random.bits (), j)) live)) in
      let cnt = if rint 10 = 0 then List.length sh else 1 + rint (min 4 (List.length sh)) in
      let rs = List.map (fun j -> Ptr j) (List.filteri (fun i _ -> i < cnt) sh) in
      (* an infix pointer as a root, and repeated roots, now and then *)
      let rs = if infix_targets <> [] && rint 3 = 0
        then (let (j, k) = pickl infix_targets in Inf (j, k)) :: rs else rs in
      if rint 3 = 0 then rs @ [pickl rs] else rs
    end in
  (objs, roots)

(* ------------------------------------------------------------------ *)
(* Hand-built heaps                                                    *)
(* ------------------------------------------------------------------ *)

let w = H.White and u = H.Blue
let o ?(tag = 0) ?(color = w) fs = { wz = List.length fs; color; tag; fields = Array.of_list fs }
let i n = Int (U64.of_int n)

(* Pad to the heap size with one white unreachable object. *)
let pad objs =
  let used = List.fold_left (fun s o -> s + o.wz + 1) 0 objs in
  let r = words - used in
  if r < 2 then failwith "hand case too big";
  Array.of_list (objs @ [ o (List.init (r - 1) (fun _ -> i 1)) ])

(* name, objects, roots, cut lists given as functions of the
   header addresses *)
let hand_cases = [
  "cycle across two ranges",
  [ o [Ptr 1]; o [Ptr 0] ], [Ptr 0],
  (fun hd -> [ [hd.(1)]; [hd.(1) + 3]; [hd.(1) + 8] ]);

  "chain bouncing between ranges",
  [ o [Ptr 1]; o [Ptr 2]; o [Ptr 3]; o [Ptr 4]; o [Ptr 5]; o [i 1] ], [Ptr 0],
  (fun hd -> [ [hd.(1); hd.(2); hd.(3); hd.(4); hd.(5)]; [hd.(2); hd.(4)]; [hd.(3)] ]);

  "infix header in another range than its closure",
  [ o ~tag:247 [i 1; i 1; Hdr 3; i 1; Ptr 2; i 1]; o [Inf (0, 3); i 1]; o [i 1] ], [Ptr 1],
  (fun hd -> [ [hd.(0) + 8 * 3]; [hd.(0) + 8 * 3; hd.(1)]; [hd.(0) + 8 * 3; hd.(2)];
               [hd.(0) + 8 * 3 + 5]; [hd.(0) + 1] ]);

  "two ranges send the same object",
  [ o [Ptr 1; Ptr 1]; o [i 1]; o [Ptr 1; Ptr 0] ], [Ptr 0; Ptr 2],
  (fun hd -> [ [hd.(1); hd.(2)]; [hd.(1)]; [hd.(2)] ]);

  "roots in every range; an unreachable cycle across ranges stays white",
  [ o [Ptr 1]; o [i 1]; o [Ptr 3]; o [Ptr 2]; o [Ptr 5]; o [i 1]; o [i 1] ], [Ptr 0; Ptr 4; Ptr 6],
  (fun hd -> [ [hd.(2); hd.(3); hd.(4)]; [hd.(3); hd.(6)] ]);

  "no roots",
  [ o [Ptr 1]; o [Ptr 0] ], [],
  (fun hd -> [ [hd.(1)] ]);

  "no-scan object in another range holds a pointer-like word",
  [ o [Ptr 1]; o ~tag:252 [Ptr 2; i 1]; o [i 1] ], [Ptr 0],
  (fun hd -> [ [hd.(1)]; [hd.(1); hd.(2)] ]);

  "cuts inside a header word and inside fields",
  [ o [Ptr 1; Ptr 2]; o [Ptr 2; i 1]; o [Ptr 0] ], [Ptr 0],
  (fun hd -> [ [hd.(1) + 1]; [hd.(1) - 1]; [hd.(0) + 12; hd.(2) + 7]; [hd.(2) + 4] ]);

  "self pointer next to free blocks",
  [ o ~color:u [i 1; i 1]; o [Ptr 1; Ptr 3]; o ~color:u [i 7]; o [i 1] ], [Ptr 1],
  (fun hd -> [ [hd.(1)]; [hd.(2)]; [hd.(3)] ]);

  "wosize-0 objects and an object with no pointers",
  [ o []; o [Ptr 0; Ptr 2]; o []; o [i 3; i 5] ], [Ptr 1; Ptr 3],
  (fun hd -> [ [hd.(1)]; [hd.(2); hd.(3)] ]);

  "infix root across a cut from its closure, and repeated roots",
  [ o ~tag:247 [i 1; i 1; Hdr 3; Ptr 1; Hdr 5; Ptr 2]; o [i 1]; o [Ptr 3]; o [i 1] ],
  [Inf (0, 3); Inf (0, 5); Ptr 0; Inf (0, 3); Ptr 3; Ptr 3],
  (fun hd -> [ [hd.(0) + 8 * 3]; [hd.(0) + 8 * 3; hd.(0) + 8 * 5]; [hd.(0) + 8 * 5; hd.(3)] ]);
]


(* Cases aimed at the design's overflow paths. *)
let more_cases = [
  "wide fan-out in one range: the stack overflows",
  [ o [Ptr 1; Ptr 2; Ptr 3; Ptr 4; Ptr 5]; o [i 1]; o [i 1]; o [Ptr 1]; o [i 1]; o [Ptr 0] ], [Ptr 0],
  (fun hd -> [ []; [hd.(3)] ]);

  "fan-out across a cut: the inbox overflows",
  [ o [Ptr 2; Ptr 3; Ptr 4; Ptr 5]; o [i 1]; o [Ptr 3]; o [i 1]; o [Ptr 5]; o [i 1] ], [Ptr 0],
  (fun hd -> [ [hd.(1)]; [hd.(1); hd.(4)] ]);

  "more roots than the stack holds",
  [ o [i 1]; o [Ptr 0]; o [i 1]; o [Ptr 2]; o [i 1] ], [Ptr 0; Ptr 1; Ptr 2; Ptr 3; Ptr 4],
  (fun hd -> [ []; [hd.(2)] ]);

  "a white child above the walk and one below it",
  [ o [i 1]; o [Ptr 0; Ptr 2]; o [i 1]; o [Ptr 1] ], [Ptr 3],
  (fun hd -> [ []; [hd.(1)]; [hd.(2)] ]);
]

let report () =
  Printf.printf "ok: %d heaps, %d cut lists, %d model runs, %d events; runs by k: 1:%d 2:%d 4:%d 8:%d\n"
    st.heaps st.cutsets st.runs st.events st.runs_k.(0) st.runs_k.(1) st.runs_k.(2) st.runs_k.(3);
  Printf.printf "coverage: %d sends, %d dropped, %d greys left off a full stack, %d setups filled a stack, %d forwards\n"
    st.sent st.dropped st.stack_full st.setup_full st.forwards;
  Printf.printf "rounds: %d fix-ups started a round, at most %d rounds in a run; %d cut lists split a reachable closure from its infix header\n"
    st.fixups st.max_rounds st.infix_split;
  Printf.printf "checks: %d read checks, %d worker steps at count 0\n" st.scrambles st.zero_reads;
  Printf.printf "reference: %d objects black, %d white objects left white; %d invalid configurations rejected\n"
    st.black st.white_left st.rejected;
  Printf.printf "roots: %d heaps with an infix root, %d with a repeated root\n" st.infix_roots st.repeat_roots;
  Printf.printf "termination: every enabled step lowered the measure; %d steps that were not enabled changed nothing or spun; effective steps at most %.2f of the initial measure\n"
    st.idle_tried st.max_ratio;
  Printf.printf "idle: %d spin steps, each kept the measure and was undone; %d Idle steps found a message had come in; %d Idle steps read 0 and stopped\n"
    st.spins st.late_msgs st.idle_stops;
  for m = 1 to nmut do
    Printf.printf "mutant %d caught %d of %d (heap %d, stuck %d, write %d, read %d, count %d)\n"
      m st.mut_caught.(m) st.mut_runs.(m) st.mut_by_heap.(m) st.mut_by_stuck.(m)
      st.mut_by_write.(m) st.mut_by_read.(m) st.mut_by_count.(m)
  done

(* fast_rt.sh rewrote FStar_Seq_Base.index/upd and FStar_UInt's bit
   operations; check them against the originals before trusting them. *)
let check_fast_rt () =
  let two64 = Z.shift_left Z.one 64 in
  let rz () = Z.erem (Z.of_int64 (Random.int64 Int64.max_int)) two64 in
  let n = Z.of_int 64 in
  for _ = 1 to 2000 do
    let a = rz () and b = rz () and sh = Z.of_int (rint 70) in
    let same what x y = if not (Z.equal x y) then begin
        Printf.printf "fast_rt: %s differs\n" what; exit 1 end in
    same "logand" (FStar_UInt.logand n a b) (FStar_UInt.logand_orig n a b);
    same "logor" (FStar_UInt.logor n a b) (FStar_UInt.logor_orig n a b);
    same "lognot" (FStar_UInt.lognot n a) (FStar_UInt.lognot_orig n a);
    same "shift_left" (FStar_UInt.shift_left n a sh) (FStar_UInt.shift_left_orig n a sh);
    same "shift_right" (FStar_UInt.shift_right n a sh) (FStar_UInt.shift_right_orig n a sh)
  done;
  for _ = 1 to 200 do
    let l = List.init (1 + rint 50) (fun _ -> rint 256) in
    let i = Z.of_int (rint (List.length l)) in
    if FStar_Seq_Base.index l i <> FStar_Seq_Base.index_orig l i
    || FStar_Seq_Base.upd l i 7 <> FStar_Seq_Base.upd_orig l i 7 then begin
      print_endline "fast_rt: Seq index/upd differ"; exit 1 end
  done

let () =
  Random.init 1;
  check_fast_rt ();
  check_rejects ();
  match Array.to_list Sys.argv |> List.tl with
  | ["hand"] ->
    Random.init 7;
    List.iter (fun (name, objs, roots, cuts) ->
        let objs = pad objs in
        Printf.printf "case: %s\n%!" name;
        run_heap objs roots ~cutsets:3 ~model_runs:40 ~mutant_runs:10 ~extra_cuts:cuts)
      (hand_cases @ more_cases);
    report ()
  | ["random"; seed; n] ->
    Random.init (int_of_string seed);
    for _ = 1 to int_of_string n do
      let (objs, roots) = gen_heap () in
      run_heap objs roots ~cutsets:3 ~model_runs:5 ~mutant_runs:2 ~extra_cuts:(fun _ -> [])
    done;
    report ()
  | _ -> prerr_endline "usage: mark_par2_test hand | random SEED N"; exit 2
