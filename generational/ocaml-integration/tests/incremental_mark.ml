(* Incremental marking (VERGC_MAJOR=incremental), from the program's side.
   =====================================================================

   With VERGC_MAJOR=incremental a major cycle marks in slices, one after each
   minor collection, and the program runs in between: it overwrites fields of
   objects the marker has already blackened and of objects it has not reached
   yet, cuts the only path to an object and stores the object somewhere else,
   stores young objects into old ones, drops references, writes into a large
   array the marker is half way through, forces lazy values and resizes hash
   tables.  What keeps marking correct is the deletion barrier (caml_modify
   greys the value it overwrites), black allocation, and the roots darkened
   when the cycle starts; what this test checks is that no live object is ever
   freed: every object is checked against a model that holds no pointers, and
   an object freed while live is reused by a later allocation, so its contents
   change and the check fails (or the program crashes).

   Nothing here can see the phase -- this file runs unchanged on stock OCaml,
   and the Makefile compares the two outputs byte for byte.  Instead every
   section runs long enough, against a small major heap, that most of it
   happens mid-cycle; the Makefile runs it under several pacings (tiny slices,
   a tiny mark stack) and checks (VERGC_MAJOR_STATS) that marking spanned
   slices with program steps in between.  Deterministic: a fixed PRNG seed. *)

let failures = ref 0

let check name ok =
  if not ok then begin
    incr failures;
    if !failures <= 20 then Printf.printf "  FAIL  %s\n%!" name
  end

let rng = Random.State.make [| 7; 14 |]
let rand n = Random.State.int rng n

(* Short-lived nursery garbage, some of it promoted: minor collections, so
   slices, between the program's steps. *)
(* How many times to run the sections (argv 1, default 1). *)
let reps = try int_of_string Sys.argv.(1) with _ -> 1
let sink = Array.make 64 []
let churn words =
  let n = ref 0 in
  while !n < words do
    let l = List.init 6 (fun i -> (i, !n)) in
    if !n mod 89 = 0 then sink.(!n land 63) <- l;
    n := !n + 6 * 6
  done

(* A payload that encodes its owner's id: a freed-and-reused block shows. *)
let payload id len = Array.init len (fun j -> id * 31 + j)
let payload_ok id len (a : int array) =
  Array.length a = len &&
  (let ok = ref true in
   for j = 0 to len - 1 do if a.(j) <> id * 31 + j then ok := false done;
   !ok)

(* ------------------------------------------------------------------------ *)
(* 1. A forest whose subtrees move.  Each node has an id, a payload and
   children; the model is the id of every node's children (ints only).  A
   move cuts a subtree from its parent -- the only path to it -- holds it in
   a local while the program allocates (minor collections, mark slices), then
   stores it under another node, which the marker may already have
   blackened.  Without the deletion barrier the subtree would be white,
   unreachable from anything the marker still scans, and freed. *)

type node = { id : int; pay : int array; mutable kids : node array }

let section_forest () =
  let nodes = 6000 and fan = 4 in
  let next_id = ref 0 in
  let mk len =
    let id = !next_id in incr next_id;
    let n = { id; pay = payload id len; kids = [||] } in
    n.kids <- Array.make fan n;          (* a node's own address: an empty slot *)
    n
  in
  (* model: the ids of every node's children (-1: an empty slot), its size *)
  let model = Array.make_matrix (nodes * 4) fan (-1) in
  let size = Array.make (nodes * 4) 0 in
  let mk len = let n = mk len in size.(n.id) <- len; n in
  let root =
    (* a few big payloads (born in the major heap), most small; each node
       under a random earlier one with a free slot (or dropped) *)
    let all = Array.init nodes (fun i -> mk (if i mod 97 = 0 then 300 else 1 + i mod 7)) in
    for i = 1 to nodes - 1 do
      let p = all.(rand i) in
      let rec place k =
        if k < fan then
          if p.kids.(k) == p then (p.kids.(k) <- all.(i); model.(p.id).(k) <- all.(i).id)
          else place (k + 1) in
      place 0
    done;
    all.(0)
  in
  (* from here on only the root (and `held`) keep the forest alive *)
  let rec pick n d =
    if d = 0 then n else
      let c = n.kids.(rand fan) in
      if c == n then n else pick c (d - 1) in
  let held = ref [] in                 (* subtrees cut and not yet re-attached *)
  let moves = ref 0 in
  let rec in_subtree s target =
    s = target || Array.exists (fun c -> c >= 0 && in_subtree c target) model.(s) in
  for round = 1 to 400 do
    (* cut a few subtrees: the parent's slot is overwritten with the parent
       itself (an empty slot); the subtree is now held only by `held` *)
    for _ = 1 to 5 do
      let p = pick root (rand 12) in
      let k = rand fan in
      if p.kids.(k) != p then begin
        let s = p.kids.(k) in
        p.kids.(k) <- p;
        model.(p.id).(k) <- -1;
        held := s :: !held
      end
    done;
    churn 3_000;
    (* re-attach them somewhere else (never under their own subtree) *)
    held := List.filter (fun s ->
        let p = pick root (rand 12) in
        let k = rand fan in
        if p.kids.(k) == p && not (in_subtree s.id p.id) then begin
          p.kids.(k) <- s; model.(p.id).(k) <- s.id; incr moves; false
        end else true) !held;
    (* replace a few leaves by fresh nodes (the old ones dropped) *)
    for _ = 1 to 3 do
      let p = pick root (rand 12) in
      let k = rand fan in
      if p.kids.(k) != p && Array.for_all (fun c -> c < 0) model.(model.(p.id).(k)) then begin
        let n = mk (1 + rand 5) in
        p.kids.(k) <- n; model.(p.id).(k) <- n.id
      end
    done;
    churn 3_000;
    if round mod 20 = 0 then begin
      (* walk the forest from the root and from the held subtrees *)
      let rec walk n =
        if not (payload_ok n.id size.(n.id) n.pay) then
          check (Printf.sprintf "forest: node %d payload" n.id) false;
        Array.iteri (fun k c ->
            let m = model.(n.id).(k) in
            if c == n then (if m >= 0 then check "forest: slot should be full" false)
            else if c.id <> m then check (Printf.sprintf "forest: node %d kid %d" n.id k) false
            else walk c) n.kids in
      walk root; List.iter walk !held
    end
  done;
  Printf.printf "forest: %d moves, %d held\n%!" !moves (List.length !held)

(* ------------------------------------------------------------------------ *)
(* 2. Large arrays scanned across slices.  A slice scans a large array a few
   fields at a time; the program swaps elements between the part already
   scanned and the part not yet scanned, cuts elements out and puts them back
   later, and overwrites elements with fresh (young, then promoted) ones. *)

let section_large () =
  let len = 60_000 in
  let a = Array.init len (fun i -> payload i 2) in
  let ids = Array.init len (fun i -> i) in
  let b = Array.init 3000 (fun i -> payload (len + i) 2) in
  let bids = Array.init 3000 (fun i -> len + i) in
  let next = ref (len + 3000) in
  for round = 1 to 120 do
    for _ = 1 to 400 do
      let i = rand len and j = rand len in
      (match rand 4 with
       | 0 -> let t = a.(i) and ti = ids.(i) in
              a.(i) <- a.(j); ids.(i) <- ids.(j); a.(j) <- t; ids.(j) <- ti
       | 1 -> let k = rand 3000 in
              let t = a.(i) and ti = ids.(i) in
              a.(i) <- b.(k); ids.(i) <- bids.(k); b.(k) <- t; bids.(k) <- ti
       | 2 -> let id = !next in incr next;
              a.(i) <- payload id 2; ids.(i) <- id
       | _ -> a.(i) <- a.(j); ids.(i) <- ids.(j))
    done;
    churn 4_000;
    if round mod 10 = 0 then begin
      Array.iteri (fun i x -> if not (payload_ok ids.(i) 2 x) then check (Printf.sprintf "large: a.(%d)" i) false) a;
      Array.iteri (fun i x -> if not (payload_ok bids.(i) 2 x) then check (Printf.sprintf "large: b.(%d)" i) false) b
    end
  done;
  Printf.printf "large: ok\n%!"

(* ------------------------------------------------------------------------ *)
(* 3. Young into old, and dropped references: an old table of lists, each
   replaced by fresh young lists (the barrier remembers the slot) or by a list
   taken from another slot (an old value moved), or emptied. *)

let section_young () =
  let n = 4000 in
  let t = Array.init n (fun i -> List.init 4 (fun j -> i * 10 + j)) in
  let keys = Array.init n (fun i -> i) in
  for round = 1 to 300 do
    for _ = 1 to 200 do
      let i = rand n in
      match rand 3 with
      | 0 -> let k = round * n + i in t.(i) <- List.init 4 (fun j -> k * 10 + j); keys.(i) <- k
      | 1 -> let j = rand n in t.(i) <- t.(j); keys.(i) <- keys.(j)
      | _ -> t.(i) <- []; keys.(i) <- -1
    done;
    churn 2_000;
    if round mod 15 = 0 then
      Array.iteri (fun i l ->
          let k = keys.(i) in
          if k < 0 then (if l <> [] then check "young: dropped" false)
          else if l <> List.init 4 (fun j -> k * 10 + j) then check (Printf.sprintf "young: slot %d" i) false) t
  done;
  Printf.printf "young: ok\n%!"

(* ------------------------------------------------------------------------ *)
(* 4. Lazy values forced mid-mark: forcing writes the result into the lazy
   block and changes its tag; the thunks allocate. *)

let section_lazy () =
  let n = 3000 in
  let mk i = lazy (Array.init (1 + i mod 9) (fun j -> i * 13 + j)) in
  let t = Array.init n mk in
  let ok i (a : int array) = Array.length a = 1 + i mod 9 && a.(0) = i * 13 in
  let gen = Array.init n (fun i -> i) in
  for round = 1 to 150 do
    for _ = 1 to 60 do
      let i = rand n in
      if rand 3 = 0 then begin
        let g = round * n + i in gen.(i) <- g; t.(i) <- mk g
      end else if not (ok gen.(i) (Lazy.force t.(i))) then check "lazy: forced value" false
    done;
    churn 3_000;
    if round mod 15 = 0 then
      Array.iteri (fun i l -> if Lazy.is_val l && not (ok gen.(i) (Lazy.force l)) then check "lazy: value" false) t
  done;
  Printf.printf "lazy: ok\n%!"

(* ------------------------------------------------------------------------ *)
(* 5. A hash table mutated and resized mid-mark, against an int model. *)

let section_hashtbl () =
  let h = Hashtbl.create 16 in
  let model = Array.make 40_000 (-1) in
  for round = 1 to 200 do
    for _ = 1 to 400 do
      let k = rand 40_000 in
      match rand 4 with
      | 0 | 1 -> let v = round * 7 + k in Hashtbl.replace h k (string_of_int v, [| v |]); model.(k) <- v
      | 2 -> Hashtbl.remove h k; model.(k) <- -1
      | _ -> (match Hashtbl.find_opt h k with
              | Some (s, a) -> if model.(k) < 0 || s <> string_of_int model.(k) || a.(0) <> model.(k) then check "hashtbl: find" false
              | None -> if model.(k) >= 0 then check "hashtbl: missing" false)
    done;
    if round mod 50 = 25 then begin Hashtbl.reset h; Array.fill model 0 40_000 (-1) end;
    churn 2_000
  done;
  let cnt = ref 0 in
  Array.iteri (fun k v -> if v >= 0 then begin
                   incr cnt;
                   match Hashtbl.find_opt h k with
                   | Some (s, a) -> if s <> string_of_int v || a.(0) <> v then check "hashtbl: final" false
                   | None -> check "hashtbl: final missing" false end) model;
  Printf.printf "hashtbl: %d bindings\n%!" !cnt

(* ------------------------------------------------------------------------ *)
(* 6. A long linked list cut and re-joined: the tail is held only by a local
   while the program allocates, then re-attached at another point. *)

type cell = { v : int; mutable next : cell option }

let section_list () =
  let n = 20_000 in
  let cells = Array.init n (fun i -> { v = i; next = None }) in
  for i = 0 to n - 2 do cells.(i).next <- Some cells.(i + 1) done;
  let head = cells.(0) in
  (* only the head is a root from here on (the array is dropped) *)
  let cells = () in ignore cells;
  let rec length c acc = match c.next with None -> acc + 1 | Some d -> length d (acc + 1) in
  let rec nth c k = if k = 0 then c else match c.next with Some d -> nth d (k - 1) | None -> c in
  for _round = 1 to 60 do
    let len = length head 0 in
    let p = nth head (1 + rand (len - 2)) in
    let tail = p.next in
    p.next <- None;                       (* the only path to the tail, cut *)
    churn 8_000;
    let q = nth head (rand (length head 0)) in
    (* re-attach the tail after q's own successor chain ends *)
    let rec last c = match c.next with None -> c | Some d -> last d in
    (last q).next <- tail;
    churn 2_000
  done;
  (* every value 0 .. n-1 is still there, exactly once *)
  let seen = Array.make n 0 in
  let rec go c = seen.(c.v) <- seen.(c.v) + 1; match c.next with Some d -> go d | None -> () in
  go head;
  Array.iteri (fun i k -> if k <> 1 then check (Printf.sprintf "list: value %d seen %d times" i k) false) seen;
  Printf.printf "list: %d cells\n%!" (length head 0)

let () =
  for _ = 1 to reps do
    section_forest ();
    section_large ();
    section_young ();
    section_lazy ();
    section_hashtbl ();
    section_list ()
  done;
  ignore (Sys.opaque_identity sink);
  if !failures = 0 then print_endline "incremental_mark: all sections passed"
  else begin
    Printf.printf "incremental_mark: %d failure(s)\n" !failures;
    exit 1
  end
