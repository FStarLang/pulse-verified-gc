(* Writes into the scanned part of an object being marked
   (VERGC_MAJOR=incremental), from the program's side.
   =====================================================================

   A mark slice scans a large object a budget's worth of fields at a time,
   and the program runs between slices.  This program keeps one large array
   alive and, between allocations (so between minor collections, so between
   mark slices), keeps writing fresh values into its first fields -- fields
   the marker scanned in an earlier slice.

   The collector once restarted the scan of the partly scanned object on such
   a write (its invariant needed the scanned fields to stay dark), so a
   program like this one kept the array's marking from ever finishing: every
   cycle stayed in the marking phase until memory ran short.  Now a scanned
   field is a scanned edge of the marking invariant, like a field of a black
   object: the barrier greys the old value, the new value is one the program
   holds, and the scan goes on where it was.  The Makefile runs this under
   small slices and checks (VERGC_MAJOR_STATS, REQUIRE_MARK_ENDS) that
   marking did end in slices, with the program running in between, and that
   no cycle had to be finished early while marking.

   What the program itself checks is that nothing it holds was freed: the
   array's elements, old and new, keep their contents.  The output is
   compared byte for byte with stock OCaml's.  Deterministic. *)

(* How many times to run (argv 1, default 1). *)
let reps = try int_of_string Sys.argv.(1) with _ -> 1

let failures = ref 0

let check name ok =
  if not ok then begin
    incr failures;
    if !failures <= 20 then Printf.printf "  FAIL  %s\n%!" name
  end

(* Short-lived garbage: minor collections, so mark slices, between the
   program's writes.  A little of it survives one round. *)
let sink = Array.make 16 []
let churn words round =
  let n = ref 0 in
  while !n < words do
    let l = List.init 6 (fun i -> i + round) in
    if !n mod 997 = 0 then sink.(!n land 15) <- l;
    n := !n + 18
  done

(* The array: well over Max_young_wosize, so allocated in the major heap,
   and long enough that marking it takes many slices.  Most of its fields
   are immediates (the marker scans them all, but there is little else to
   mark), every 100th a small list. *)
let len = 60_000
let elt i = if i mod 100 = 0 then [i; -i] else []

(* How many leading fields the program keeps rewriting. *)
let hot = 8

let run rounds =
  let a = Array.make len [] in
  for i = 0 to len - 1 do a.(i) <- elt i done;
  for r = 1 to rounds do
    (* fresh (young) values into fields the marker has already scanned *)
    for j = 0 to hot - 1 do a.(j) <- [r; j] done;
    churn 40_000 r;
    (* and an old value moved into the hot part *)
    if r mod 64 = 0 then a.(r mod hot) <- a.(100 * (1 + r mod (len / 100 - 1)))
  done;
  (* nothing the array holds was freed *)
  for j = 0 to hot - 1 do
    let ok =
      match a.(j) with
      | [x; y] ->
          (x = rounds && y = j) ||
          (rounds mod 64 = 0 && j = rounds mod hot &&
           x = 100 * (1 + rounds mod (len / 100 - 1)) && y = - x)
      | _ -> false in
    check (Printf.sprintf "hot field %d" j) ok
  done;
  let sum = ref 0 in
  for i = hot to len - 1 do
    if a.(i) <> elt i then check (Printf.sprintf "field %d" i) false;
    sum := !sum + List.fold_left (+) i a.(i)
  done;
  !sum

let () =
  let total = ref 0 in
  for _ = 1 to reps do
    total := !total + run 3_000
  done;
  Array.iter (fun l -> check "sink" (List.length l = 0 || List.length l = 6)) sink;
  Printf.printf "mark_scanned_writes: %d failures, checksum %d\n" !failures !total;
  if !failures > 0 then exit 1
