(* recursive_fib.ml - Recursive computation with allocations
 * Fibonacci with memoization (allocates hash table entries)
 * Usage: ./recursive_fib <n>  (default: 40)
 *)

let memo = Hashtbl.create 100

let rec fib n =
  if n <= 1 then n
  else
    match Hashtbl.find_opt memo n with
    | Some v -> v
    | None ->
      let v = fib (n - 1) + fib (n - 2) in
      Hashtbl.add memo n v;
      v

let () =
  let n = try int_of_string Sys.argv.(1) with _ -> 40 in
  
  (* Run multiple times to stress GC *)
  let total = ref 0 in
  for i = 1 to 1000 do
    Hashtbl.clear memo;
    total := !total + fib (n + (i mod 5))
  done;
  
  Gc.full_major ();
  let stats = Gc.stat () in
  
  Printf.printf "Total: %d\n" !total;
  Printf.printf "Minor collections: %d\n" stats.minor_collections;
  Printf.printf "Major collections: %d\n" stats.major_collections
