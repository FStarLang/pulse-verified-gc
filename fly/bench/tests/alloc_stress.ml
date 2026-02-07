(* alloc_stress.ml - Heavy allocation benchmark
 * Allocates many small objects rapidly
 * Usage: ./alloc_stress <count>  (default: 10_000_000)
 *)

let () =
  let n = try int_of_string Sys.argv.(1) with _ -> 10_000_000 in
  let sum = ref 0 in
  
  for i = 1 to n do
    (* Allocate a list of 3 elements - small but frequent *)
    let lst = [i; i+1; i+2] in
    sum := !sum + List.hd lst
  done;
  
  Printf.printf "Sum: %d\n" !sum;
  
  (* Force a full GC and report stats *)
  Gc.full_major ();
  let stats = Gc.stat () in
  Printf.printf "Minor collections: %d\n" stats.minor_collections;
  Printf.printf "Major collections: %d\n" stats.major_collections
