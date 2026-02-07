(* hashtbl_stress.ml - Hash table stress test
 * Many insertions and lookups with GC pressure
 * Usage: ./hashtbl_stress <size>  (default: 1_000_000)
 *)

let () =
  let n = try int_of_string Sys.argv.(1) with _ -> 1_000_000 in
  
  let tbl = Hashtbl.create (n / 10) in
  
  (* Insert n elements *)
  for i = 1 to n do
    Hashtbl.add tbl i (string_of_int i)
  done;
  
  (* Look up all elements *)
  let found = ref 0 in
  for i = 1 to n do
    match Hashtbl.find_opt tbl i with
    | Some _ -> incr found
    | None -> ()
  done;
  
  (* Remove half *)
  for i = 1 to n / 2 do
    Hashtbl.remove tbl i
  done;
  
  Gc.full_major ();
  let stats = Gc.stat () in
  
  Printf.printf "Found: %d\n" !found;
  Printf.printf "Remaining: %d\n" (Hashtbl.length tbl);
  Printf.printf "Minor collections: %d\n" stats.minor_collections;
  Printf.printf "Major collections: %d\n" stats.major_collections
