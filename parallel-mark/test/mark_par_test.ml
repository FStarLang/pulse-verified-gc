(* Stage 1 test: run the extracted parallel mark model, GC.Spec.MarkPar, under
   random interleavings, and compare it with the extracted
   GC.Spec.MarkPar.sequential_mark_x (which F* proves equal to
   GC.Spec.Mark.mark after greying the roots).

     mark_par_test hand              hand-built cases
     mark_par_test random SEED N     N generated heaps

   The heap size is fixed per process (PS_WORDS, see GC_Spec_ZeroAddr.ml).
   The first failure of the model stops the run with exit 1 and a full
   description.  The mutants (GC.Spec.MarkPar.Mutants) are run on the same
   cases, and the number each one is caught on is printed as
   "mutant M caught C of R". *)

module U64 = Stdint.Uint64
module Seq = FStar_Seq_Base
module H = GC_Lib_Header
module MP = GC_Spec_MarkPar_Model
module MU = GC_Spec_MarkPar_Mutants
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

type stats = {
  mutable heaps : int; mutable cutsets : int; mutable runs : int; mutable events : int;
  mutable runs_k : int array;          (* by k = 1, 2, 4, 8, other *)
  mutable sent : int;                  (* messages sent between ranges *)
  mutable max_net : int;               (* most messages in transit at once *)
  mutable reordered : int;             (* deliveries of a message that was not the oldest *)
  mutable infix_split : int;           (* cut sets putting a reachable infix header in another range than its closure *)
  mutable black : int; mutable white_left : int;
  mutable rejected : int;              (* invalid cut lists rejected *)
  mutable idle_tried : int;            (* steps tried that were not enabled *)
  mutable max_ratio : float;           (* effective steps / initial measure, at most *)
  mutable infix_roots : int; mutable repeat_roots : int;
  mut_runs : int array; mut_caught : int array;
  mut_by_heap : int array; mut_by_owner : int array;
}

let st = { heaps = 0; cutsets = 0; runs = 0; events = 0; runs_k = Array.make 5 0;
           sent = 0; max_net = 0; reordered = 0; infix_split = 0;
           black = 0; white_left = 0; rejected = 0; idle_tried = 0; max_ratio = 0.;
           infix_roots = 0; repeat_roots = 0;
           mut_runs = Array.make 5 0; mut_caught = Array.make 5 0;
           mut_by_heap = Array.make 5 0; mut_by_owner = Array.make 5 0 }

let kslot k = match k with 1 -> 0 | 2 -> 1 | 4 -> 2 | 8 -> 3 | _ -> 4

(* ------------------------------------------------------------------ *)
(* Describing a failure                                                *)
(* ------------------------------------------------------------------ *)

let zl = List.map Z.of_int
let owner cs x = Z.to_int (MP.owner (zl cs) (U64.of_int x))

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
  | MP.Pop i -> Printf.sprintf "Pop %s" (Z.to_string i)
  | MP.Scan i -> Printf.sprintf "Scan %s" (Z.to_string i)
  | MP.Take i -> Printf.sprintf "Take %s" (Z.to_string i)
  | MP.Deliver j -> Printf.sprintf "Deliver %s" (Z.to_string j)

let first_diff (a : int list) (b : int list) =
  let rec go i = function
    | x :: xs, y :: ys -> if x <> y then Some i else go (i + 1) (xs, ys)
    | _ -> None in
  go 0 (a, b)

let bytes (h : GC_Spec_Base.heap) : int list = Seq.seq_to_list h

let fail what g cs roots sched (hs : GC_Spec_Base.heap) (hp : GC_Spec_Base.heap) =
  Printf.printf "FAILURE: %s\n" what;
  print_string (describe g cs roots);
  Printf.printf "schedule (%d events): %s\n" (List.length sched)
    (String.concat ", " (List.map ev_name sched));
  (match first_diff (bytes hs) (bytes hp) with
   | None -> print_string "heaps equal\n"
   | Some i ->
     let a = i land (lnot 7) in
     Printf.printf "heaps differ first in the word @%d: sequential %s, parallel %s\n"
       a (U64.to_string (rw hs a)) (U64.to_string (rw hp a)));
  exit 1

(* ------------------------------------------------------------------ *)
(* Schedulers                                                          *)
(* ------------------------------------------------------------------ *)

let nstrategies = 5
let strategy_name = [| "uniform"; "late delivery"; "newest first"; "one worker"; "round robin" |]

let is_deliver = function MP.Deliver _ -> true | _ -> false
let actor e = Z.to_int (MP.actor e)

(* Strategy state: the worker in focus, or the round-robin position. *)
let choose strat cur (en : MP.event list) =
  let own = List.filter (fun e -> not (is_deliver e)) en in
  let dl = List.filter is_deliver en in
  match strat with
  | 0 -> pickl en
  | 1 -> if own <> [] then pickl own else pickl dl
  | 2 -> if dl <> [] && rint 2 = 0 then List.nth dl (List.length dl - 1) else pickl en
  | 3 ->
    let mine = List.filter (fun e -> actor e = !cur) own in
    if mine <> [] && rint 10 < 9 then pickl mine
    else (let e = pickl en in if not (is_deliver e) then cur := actor e; e)
  | _ ->
    if own = [] || (dl <> [] && rint 10 < 3) then pickl (if dl <> [] then dl else en)
    else begin
      let ws = List.sort_uniq compare (List.map actor own) in
      let next = match List.filter (fun w -> w >= !cur) ws with w :: _ -> w | [] -> List.hd ws in
      cur := next + 1;
      pickl (List.filter (fun e -> actor e = next) own)
    end

(* ------------------------------------------------------------------ *)
(* One run                                                             *)
(* ------------------------------------------------------------------ *)

let limit = 200000

(* Every byte the step changed lies in the header of an enumerated object
   that the acting worker owns. *)
let owner_ok objset cs e (h0 : GC_Spec_Base.heap) (h1 : GC_Spec_Base.heap) =
  let rec go i a b =
    match a, b with
    | x :: xs, y :: ys ->
      if x <> y then begin
        let o = (i land (lnot 7)) + 8 in
        if is_deliver e || not (Hashtbl.mem objset o) || owner cs o <> actor e then false
        else go (i + 1) xs ys
      end else go (i + 1) xs ys
    | _ -> true in
  go 0 (bytes h0) (bytes h1)

(* Run mutant m (0 = the model) under strategy strat until it stops.
   Returns (final heap, ownership respected, schedule). *)
let run_one m strat cs g roots objset =
  let zcs = zl cs in
  let r64 = List.map U64.of_int roots in
  let s = ref (MP.init zcs g r64) in
  let sched = ref [] in
  let steps = ref 0 in
  let own = ref true in
  let cur = ref 0 in
  let zm = Z.of_int m in
  while not (MU.quiescent_m zm !s) do
    let en = MP.enabled !s in
    if en = [] then begin
      Printf.printf "no event enabled, but not quiescent (mutant %d)\n" m;
      fail "enabled is empty before the end" g cs roots (List.rev !sched) g !s.MP.heap
    end;
    let e = choose strat cur en in
    let s' = if m = 0 then MP.step zcs !s e else MU.step_m zm zcs !s e in
    if m = 0 then begin
      (* termination: an enabled step lowers the measure; a step that is
         not enabled changes nothing *)
      let ms = Z.to_int (MP.measure !s) and ms' = Z.to_int (MP.measure s') in
      if ms' >= ms then
        fail (Printf.sprintf "%s did not lower the measure (%d -> %d)" (ev_name e) ms ms')
          g cs roots (List.rev (e :: !sched)) !s.MP.heap s'.MP.heap;
      if rint 8 = 0 then begin
        let k = List.length cs + 1 and n = List.length !s.MP.net in
        let d = match rint 4 with
          | 0 -> MP.Pop (Z.of_int (rint (k + 1))) | 1 -> MP.Scan (Z.of_int (rint (k + 1)))
          | 2 -> MP.Take (Z.of_int (rint (k + 1))) | _ -> MP.Deliver (Z.of_int (rint (n + 2))) in
        if not (List.mem d en) then begin
          st.idle_tried <- st.idle_tried + 1;
          if MP.step zcs !s d <> !s then
            fail (Printf.sprintf "%s is not enabled but changed the state" (ev_name d))
              g cs roots (List.rev !sched) !s.MP.heap !s.MP.heap
        end
      end;
      if MU.step_m zm zcs !s e <> s' then
        fail "step_m 0 differs from step" g cs roots (List.rev (e :: !sched)) g s'.MP.heap;
      let n0 = List.length !s.MP.net and n1 = List.length s'.MP.net in
      if n1 > n0 then st.sent <- st.sent + 1;
      st.max_net <- max st.max_net n1;
      (match e with MP.Deliver j when Z.to_int j > 0 -> st.reordered <- st.reordered + 1 | _ -> ())
    end;
    if not (owner_ok objset cs e !s.MP.heap s'.MP.heap) then begin
      own := false;
      if m = 0 then
        fail (Printf.sprintf "%s wrote outside its own objects' headers" (ev_name e))
          g cs roots (List.rev (e :: !sched)) !s.MP.heap s'.MP.heap
    end;
    s := s';
    sched := e :: !sched;
    incr steps;
    if !steps > limit then begin
      if m = 0 then fail "no end after the step limit" g cs roots [] g !s.MP.heap;
      s := { !s with MP.workers = [] ; MP.net = [] }
    end
  done;
  if m = 0 then begin
    if MP.enabled !s <> [] then fail "quiescent, but an event is enabled" g cs roots (List.rev !sched) g !s.MP.heap;
    let m0 = Z.to_int (MP.measure (MP.init zcs g r64)) in
    if !steps > m0 then fail "more effective steps than the initial measure" g cs roots (List.rev !sched) g !s.MP.heap;
    if MP.effective_steps zcs (MP.init zcs g r64) (List.rev !sched) <> Z.of_int !steps then
      fail "effective_steps miscounts" g cs roots (List.rev !sched) g !s.MP.heap;
    st.max_ratio <- max st.max_ratio (float !steps /. float (max 1 m0));
    st.events <- st.events + !steps
  end;
  (!s.MP.heap, !own, List.rev !sched)

(* ------------------------------------------------------------------ *)
(* One heap                                                            *)
(* ------------------------------------------------------------------ *)

(* Check the reference itself against the plain search, as
   mark_par_reachable states it: exactly the reachable objects are black,
   each with its original header made black; every other word unchanged. *)
let check_reference g roots (hs : GC_Spec_Base.heap) =
  let r = reach g roots in
  let objs = objects g in
  let hdr_of = Hashtbl.create 64 in
  List.iter (fun x ->
      let b = X.is_black_x (U64.of_int x) hs in
      if b <> Hashtbl.mem r x then fail "reference: black is not reachable" g [] roots [] g hs;
      if b then begin
        st.black <- st.black + 1;
        Hashtbl.replace hdr_of (x - 8) ();
        if rw hs (x - 8) <> rw (X.makeBlack_x (U64.of_int x) g) (x - 8) then
          fail "reference: header is not the original made black" g [] roots [] g hs
      end else if col_at g x = H.White then st.white_left <- st.white_left + 1)
    objs;
  let a = ref 0 in
  while !a < hsize do
    if not (Hashtbl.mem hdr_of !a) && rw hs !a <> rw g !a then
      fail (Printf.sprintf "reference: word @%d changed" !a) g [] roots [] g hs;
    a := !a + 8
  done

(* Cut lists the model must reject. *)
let check_rejects () =
  let bad = [ [zero]; [hsize]; [zero + 9; zero + 9]; [zero + 17; zero + 9]; [hsize + 3] ] in
  List.iter (fun cs ->
      if MP.valid_cuts (zl cs) then begin
        Printf.printf "valid_cuts accepted [%s]\n" (String.concat "; " (List.map string_of_int cs));
        exit 1
      end;
      st.rejected <- st.rejected + 1)
    bad

(* k - 1 distinct cuts.  Each is drawn from one of: any address; a header;
   just inside a header word or an object's first field; between a
   closure's header and one of its infix headers. *)
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

(* (closure, infix) address pairs, reachable or not, read from the heap. *)
let infix_pairs g =
  List.concat_map (fun o ->
      if tag_at g o = 247 then
        List.filter_map (fun (i, v) ->
            if U64.to_int (GC_Spec_Object.getTag v) = 249 then Some (o, o + 8 * i) else None)
          (List.mapi (fun i v -> (i + 1, v)) (fields g o))
      else [])
    (objects g)

let run_case g cs roots ~model_runs ~mutant_runs =
  if not (MP.valid_cuts (zl cs)) then fail "valid_cuts rejected a generated cut list" g cs roots [] g g;
  let k = List.length cs + 1 in
  st.cutsets <- st.cutsets + 1;
  let objset = Hashtbl.create 64 in
  List.iter (fun o -> Hashtbl.replace objset o ()) (objects g);
  let r = reach g roots in
  if List.exists (fun (c, d) -> Hashtbl.mem r c && owner cs (d) <> owner cs c) (infix_pairs g) then
    st.infix_split <- st.infix_split + 1;
  let hs = MP.sequential_mark_x g (List.map U64.of_int roots) in
  for n = 0 to model_runs - 1 do
    let strat = n mod nstrategies in
    let (hp, _, sched) = run_one 0 strat cs g roots objset in
    st.runs <- st.runs + 1;
    st.runs_k.(kslot k) <- st.runs_k.(kslot k) + 1;
    if bytes hp <> bytes hs then
      fail (Printf.sprintf "parallel heap differs from the sequential mark (%s)" strategy_name.(strat))
        g cs roots sched hs hp;
    let hr = (MP.run (zl cs) g (List.map U64.of_int roots) sched).MP.heap in
    if bytes hr <> bytes hp then fail "replaying the schedule through run differs" g cs roots sched hp hr
  done;
  for m = 1 to 4 do
    for n = 0 to mutant_runs - 1 do
      let strat = n mod nstrategies in
      let (hp, own, _) = run_one m strat cs g roots objset in
      st.mut_runs.(m) <- st.mut_runs.(m) + 1;
      let by_heap = bytes hp <> bytes hs in
      if by_heap then st.mut_by_heap.(m) <- st.mut_by_heap.(m) + 1;
      if not own then st.mut_by_owner.(m) <- st.mut_by_owner.(m) + 1;
      if by_heap || not own then st.mut_caught.(m) <- st.mut_caught.(m) + 1
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
  check_reference g roots (MP.sequential_mark_x g (List.map U64.of_int roots));
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

(* ------------------------------------------------------------------ *)
(* Main                                                                *)
(* ------------------------------------------------------------------ *)

let report () =
  Printf.printf "ok: %d heaps, %d cut lists, %d model runs, %d events; runs by k: 1:%d 2:%d 4:%d 8:%d\n"
    st.heaps st.cutsets st.runs st.events st.runs_k.(0) st.runs_k.(1) st.runs_k.(2) st.runs_k.(3);
  Printf.printf "coverage: %d messages sent, at most %d in transit, %d out-of-order deliveries, %d cut lists split a reachable closure from its infix header\n"
    st.sent st.max_net st.reordered st.infix_split;
  Printf.printf "reference: %d objects black, %d white objects left white; %d invalid cut lists rejected\n"
    st.black st.white_left st.rejected;
  Printf.printf "roots: %d heaps with an infix root, %d with a repeated root\n" st.infix_roots st.repeat_roots;
  Printf.printf "termination: every step lowered the measure; %d steps that were not enabled changed nothing; effective steps at most %.2f of the initial measure\n"
    st.idle_tried st.max_ratio;
  for m = 1 to 4 do
    Printf.printf "mutant %d caught %d of %d (heap differs %d, owner rule broken %d)\n"
      m st.mut_caught.(m) st.mut_runs.(m) st.mut_by_heap.(m) st.mut_by_owner.(m)
  done

let () =
  check_rejects ();
  match Array.to_list Sys.argv |> List.tl with
  | ["hand"] ->
    Random.init 7;
    List.iter (fun (name, objs, roots, cuts) ->
        let objs = pad objs in
        Printf.printf "case: %s\n%!" name;
        run_heap objs roots ~cutsets:3 ~model_runs:40 ~mutant_runs:10 ~extra_cuts:cuts)
      hand_cases;
    report ()
  | ["random"; seed; n] ->
    Random.init (int_of_string seed);
    for _ = 1 to int_of_string n do
      let (objs, roots) = gen_heap () in
      run_heap objs roots ~cutsets:3 ~model_runs:5 ~mutant_runs:2 ~extra_cuts:(fun _ -> [])
    done;
    report ()
  | _ -> prerr_endline "usage: mark_par_test hand | random SEED N"; exit 2
