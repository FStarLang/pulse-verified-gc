(* string_concat.ml - String manipulation benchmark
 * Many string allocations and concatenations
 * Usage: ./string_concat <iterations>  (default: 100_000)
 *)

let () =
  let n = try int_of_string Sys.argv.(1) with _ -> 100_000 in
  
  (* Build strings in a buffer *)
  let buf = Buffer.create 1024 in
  for i = 1 to n do
    Buffer.add_string buf (string_of_int i);
    Buffer.add_char buf ' ';
    if i mod 1000 = 0 then begin
      let _ = Buffer.contents buf in
      Buffer.clear buf
    end
  done;
  
  (* Also do raw concatenation (slower, more GC) *)
  let result = ref "" in
  for i = 1 to n / 100 do
    result := !result ^ string_of_int i
  done;
  
  Gc.full_major ();
  let stats = Gc.stat () in
  
  Printf.printf "Result length: %d\n" (String.length !result);
  Printf.printf "Minor collections: %d\n" stats.minor_collections;
  Printf.printf "Major collections: %d\n" stats.major_collections
