(* array_ops.ml - Array operations benchmark
 * Array creation, copying, and transformation
 * Usage: ./array_ops <size>  (default: 10_000_000)
 *)

let () =
  let n = try int_of_string Sys.argv.(1) with _ -> 10_000_000 in
  
  (* Create array *)
  let arr1 = Array.init n (fun i -> i) in
  
  (* Map operation (creates new array) *)
  let arr2 = Array.map (fun x -> x * 2) arr1 in
  
  (* Filter-like operation *)
  let arr3 = Array.of_list (
    List.filter (fun x -> x mod 2 = 0) (Array.to_list arr2)
  ) in
  
  (* Fold *)
  let sum = Array.fold_left (+) 0 arr3 in
  
  Gc.full_major ();
  let stats = Gc.stat () in
  
  Printf.printf "Sum: %d\n" sum;
  Printf.printf "Array3 length: %d\n" (Array.length arr3);
  Printf.printf "Minor collections: %d\n" stats.minor_collections;
  Printf.printf "Major collections: %d\n" stats.major_collections
