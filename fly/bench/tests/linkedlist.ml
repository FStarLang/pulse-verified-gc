(* linkedlist.ml - Linked list manipulation benchmark
 * Stresses pointer-heavy data structures
 * Usage: ./linkedlist <size>  (default: 1_000_000)
 *)

let rec build_list n acc =
  if n <= 0 then acc
  else build_list (n - 1) (n :: acc)

let rec reverse_acc acc = function
  | [] -> acc
  | x :: xs -> reverse_acc (x :: acc) xs

let reverse lst = reverse_acc [] lst

let rec sum_list acc = function
  | [] -> acc
  | x :: xs -> sum_list (acc + x) xs

let () =
  let n = try int_of_string Sys.argv.(1) with _ -> 1_000_000 in
  
  (* Build, reverse, sum - repeat *)
  let total = ref 0 in
  for _ = 1 to 10 do
    let lst = build_list n [] in
    let rev = reverse lst in
    total := !total + sum_list 0 rev
  done;
  
  Gc.full_major ();
  let stats = Gc.stat () in
  
  Printf.printf "Total: %d\n" !total;
  Printf.printf "Minor collections: %d\n" stats.minor_collections;
  Printf.printf "Major collections: %d\n" stats.major_collections
