let n = try int_of_string Sys.argv.(1) with _ -> 300_000

let () =
  let b = Bytes.make n 'x' in
  Bytes.set b (n - 1) 'y';
  Printf.printf "major_expand %d %c\n" (Bytes.length b) (Bytes.get b (n - 1))
