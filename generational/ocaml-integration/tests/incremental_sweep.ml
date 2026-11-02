(* The incremental sweep (VERGC_SWEEP=incremental), from the program's side.
   =========================================================================

   With VERGC_SWEEP=incremental a full collection marks and then sweeps the
   major heap in slices, one after each minor collection, so the program runs
   -- allocates, mutates, collects -- while the sweep is half done.  The
   collector colours a block allocated in front of the sweep cursor black (the
   sweep keeps it) and one behind it white; a minor collection mid-sweep keeps
   the sweep where it is; a full collection requested mid-sweep finishes the
   sweep first; a failed allocation mid-sweep finishes the sweep and retries.

   Nothing here can see the phase -- this file runs unchanged on stock OCaml,
   and the Makefile compares the two outputs byte for byte.  Instead every
   section runs long enough, against a small major heap, that most of it
   happens mid-sweep, and the Makefile checks (VERGC_SWEEP_STATS) that it did:
   slices were run, and major allocations happened while sweeping.  It runs
   with two pacings: the default, and tiny slices (VERGC_SWEEP_MIN_WORDS=256,
   VERGC_SWEEP_K=0), where a sweep spans thousands of minor collections and
   most full collections are requested mid-sweep.

   Each section keeps a model of what it stored and checks every live object
   against it.  An object the sweep freed while live is reused by a later
   allocation, so its contents change and the check fails (or the program
   crashes).  Deterministic: a fixed PRNG seed, no timing dependence. *)

[@@@ocaml.warning "-3"]   (* Obj.truncate is deprecated *)

let failures = ref 0

let check name ok =
  if not ok then begin
    incr failures;
    Printf.printf "  FAIL  %s\n%!" name
  end

let rng = Random.State.make [| 42 |]
let rand n = Random.State.int rng n

(* A major block (wosize > 256 is born in the major heap) whose every field
   encodes its key, so a block freed and reused is detected. *)
let big key len = Array.init len (fun j -> key * 1000 + j)

let big_ok key len (a : int array) =
  Array.length a = len
  && (let ok = ref true in
      for j = 0 to len - 1 do if a.(j) <> key * 1000 + j then ok := false done;
      !ok)

(* Short-lived nursery garbage, with some survivors to promote. *)
let sink = ref []
let churn words =
  let n = ref 0 in
  while !n < words do
    let l = List.init 8 (fun i -> (i, !n)) in
    if !n mod 97 = 0 then sink := l :: (match !sink with _ :: _ :: t when List.length t > 200 -> t | s -> s);
    n := !n + 8 * 6
  done

(* 1. Allocation during the sweep, and objects allocated in front of the
   cursor surviving it.  A table of live major blocks; every round replaces a
   random tenth of it (the old blocks become garbage the sweep frees) and
   churns the nursery (minor collections, so slices). *)
let section_alloc () =
  let n = 400 and len = 300 in
  let keys = Array.init n (fun i -> i) in
  let tbl = Array.init n (fun i -> big i len) in
  let next = ref n in
  for _round = 1 to 300 do
    for _ = 1 to n / 10 do
      let i = rand n in
      keys.(i) <- !next;
      tbl.(i) <- big !next len;
      incr next
    done;
    churn 20_000;
    for i = 0 to n - 1 do
      if not (big_ok keys.(i) len tbl.(i)) then
        check (Printf.sprintf "alloc: block %d (key %d)" i keys.(i)) false
    done
  done;
  Printf.printf "alloc: %d blocks allocated\n%!" !next

(* 2. Many minor collections mid-sweep: a long-lived structure of small
   (promoted) objects, rebuilt piecewise, checked after every round. *)
let section_minor () =
  let n = 2000 in
  let cells = Array.init n (fun i -> ref (i, string_of_int i)) in
  for round = 1 to 400 do
    for _ = 1 to 200 do
      let i = rand n in
      let k = round * n + i in
      cells.(i) <- ref (k, string_of_int k)
    done;
    churn 30_000;
    Array.iteri (fun i r ->
        let (k, s) = !r in
        if k mod n <> i || s <> string_of_int k then
          check (Printf.sprintf "minor: cell %d" i) false)
      cells
  done;
  Printf.printf "minor: ok\n%!"

(* 3. Mutation of old objects mid-sweep: an old major array gets young
   pointers (fresh tuples, which the write barrier remembers) and old ones
   (major blocks allocated earlier or mid-sweep). *)
let section_mutate () =
  let n = 1000 in
  let old : (int * int array) array = Array.make n (0, [||]) in
  let olds = Array.init 50 (fun i -> big (100_000 + i) 260) in
  for i = 0 to n - 1 do old.(i) <- (i, olds.(i mod 50)) done;
  for round = 1 to 300 do
    for _ = 1 to 100 do
      let i = rand n in
      if rand 2 = 0 then
        (* young: a fresh tuple pointing at a fresh small array *)
        old.(i) <- (round * n + i, Array.make 3 (round * n + i))
      else begin
        (* old: an existing major block, or one allocated now, mid-sweep *)
        let j = rand 50 in
        if rand 4 = 0 then olds.(j) <- big (200_000 + round * 50 + j) 260;
        old.(i) <- (round * n + i, olds.(j))
      end
    done;
    churn 20_000;
    Array.iteri (fun i (k, a) ->
        if k mod n <> i && k <> i then check (Printf.sprintf "mutate: key %d" i) false;
        let l = Array.length a in
        if l = 3 then (if a.(0) <> k || a.(2) <> k then check "mutate: young payload" false)
        else if l = 260 then begin
          let key = a.(0) / 1000 in
          if not (big_ok key 260 a) then check "mutate: old payload" false
        end else check (Printf.sprintf "mutate: length %d" l) false)
      old
  done;
  Printf.printf "mutate: ok\n%!"

(* 4. Large arrays: big blocks (a sweep slice steps over one in a single
   step, overshooting its budget), kept and dropped. *)
let section_large () =
  let keep = Array.make 4 [||] in
  let keys = Array.make 4 0 in
  for round = 1 to 40 do
    let len = 20_000 + rand 120_000 in
    let i = rand 4 in
    keep.(i) <- big round len; keys.(i) <- round;
    ignore (Sys.opaque_identity (Array.make (10_000 + rand 100_000) round));  (* garbage *)
    churn 50_000;
    Array.iteri (fun i a ->
        if Array.length a > 0 && not (big_ok keys.(i) (Array.length a) a) then
          check (Printf.sprintf "large: slot %d" i) false)
      keep
  done;
  Printf.printf "large: ok\n%!"

(* 5. Full collections requested mid-sweep (Gc.full_major, Gc.major,
   Gc.compact finish the sweep first), and Gc.major_slice. *)
let section_explicit () =
  let n = 300 in
  let tbl = Array.init n (fun i -> big i 280) in
  let keys = Array.init n (fun i -> i) in
  for round = 1 to 60 do
    for _ = 1 to 30 do
      let i = rand n in
      keys.(i) <- round * n + i; tbl.(i) <- big keys.(i) 280
    done;
    churn 10_000;
    (match round mod 4 with
     | 0 -> Gc.full_major ()
     | 1 -> Gc.major ()
     | 2 -> ignore (Gc.major_slice 0)
     | _ -> Gc.compact ());
    Array.iteri (fun i a -> if not (big_ok keys.(i) 280 a) then
                    check (Printf.sprintf "explicit: block %d" i) false) tbl
  done;
  Printf.printf "explicit: ok\n%!"

(* 6. Obj.truncate (its leftover header takes the allocation colour) and
   Marshal (intern carves one major block into many objects with the colour
   the block got) mid-sweep. *)
let section_truncate_intern () =
  let n = 100 in
  let tbl = Array.init n (fun i -> big i 400) in
  let lens = Array.make n 400 in
  let data = List.init 2000 (fun i -> (i, string_of_int i, [| i; i + 1 |])) in
  let blob = Marshal.to_string data [] in
  let interned = Array.make 8 data in
  for round = 1 to 80 do
    let i = rand n in
    if lens.(i) > 300 then begin
      let l = 300 + rand (lens.(i) - 300) in
      Obj.truncate (Obj.repr tbl.(i)) l; lens.(i) <- l
    end else begin
      tbl.(i) <- big (round * n + i) 400; lens.(i) <- 400
    end;
    interned.(rand 8) <- (Marshal.from_string blob 0 : (int * string * int array) list);
    churn 20_000;
    Array.iteri (fun i a ->
        if Array.length a <> lens.(i) then check "truncate: length" false
        else begin
          let key = a.(0) / 1000 in
          for j = 0 to lens.(i) - 1 do
            if a.(j) <> key * 1000 + j then check "truncate: payload" false
          done
        end) tbl;
    Array.iter (fun d -> if d <> data then check "intern: data" false) interned
  done;
  Printf.printf "truncate/intern: ok\n%!"

(* 7. Stress: a random mix of everything above against a model. *)
let section_stress () =
  let n = 3000 in
  let slots : int array array = Array.make n [||] in
  let keys = Array.make n (-1) in
  let pairs : (int * int list) array = Array.make 500 (0, []) in
  for step = 1 to 60_000 do
    let i = rand n in
    (match rand 10 with
     | 0 | 1 | 2 -> keys.(i) <- step; slots.(i) <- big step (1 + rand 600)
     | 3 -> keys.(i) <- -1; slots.(i) <- [||]
     | 4 | 5 -> let j = rand 500 in pairs.(j) <- (step, List.init (rand 20) (fun x -> x + step))
     | 6 -> let j = rand n in keys.(i) <- keys.(j); slots.(i) <- slots.(j)
     | 7 -> if step mod 5000 = 0 then Gc.full_major ()
     | _ -> churn 2_000);
    if step mod 2000 = 0 then begin
      Array.iteri (fun i a ->
          if keys.(i) >= 0 && not (big_ok keys.(i) (Array.length a) a) then
            check (Printf.sprintf "stress: slot %d" i) false) slots;
      Array.iter (fun (k, l) ->
          List.iteri (fun x v -> if v <> x + k then check "stress: list" false) l) pairs
    end
  done;
  let sum = ref 0 in
  Array.iteri (fun i a -> if keys.(i) >= 0 then sum := (!sum + keys.(i) * Array.length a) land 0xFFFFFF) slots;
  Printf.printf "stress: checksum %d\n%!" !sum

let () =
  section_alloc ();
  section_minor ();
  section_mutate ();
  section_large ();
  section_explicit ();
  section_truncate_intern ();
  section_stress ();
  ignore (Sys.opaque_identity !sink);
  if !failures = 0 then print_endline "incremental_sweep: all sections passed"
  else begin
    Printf.printf "incremental_sweep: %d failure(s)\n" !failures;
    exit 1
  end
