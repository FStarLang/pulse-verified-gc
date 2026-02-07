(* multicore_alloc.ml - Multicore allocation stress test
 * Multiple domains allocating concurrently
 * Usage: ./multicore_alloc <n_domains> <iterations>  (default: 4 100000)
 *)

let worker id iterations =
  let sum = ref 0 in
  for i = 1 to iterations do
    (* Allocate arrays that will need GC *)
    let arr = Array.init 100 (fun j -> ref (i + j + id * 1000)) in
    sum := !sum + !(arr.(0))
  done;
  !sum

let () =
  let n_domains = try int_of_string Sys.argv.(1) with _ -> 4 in
  let iterations = try int_of_string Sys.argv.(2) with _ -> 100_000 in
  
  let domains = Array.init n_domains (fun i ->
    Domain.spawn (fun () -> worker i iterations)
  ) in
  
  let results = Array.map Domain.join domains in
  let total = Array.fold_left (+) 0 results in
  
  Gc.full_major ();
  let stats = Gc.stat () in
  
  Printf.printf "Total: %d\n" total;
  Printf.printf "Minor collections: %d\n" stats.minor_collections;
  Printf.printf "Major collections: %d\n" stats.major_collections
