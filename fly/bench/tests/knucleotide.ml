(*
 * The Computer Language Benchmarks Game
 * https://salsa.debian.org/benchmarksgame-team/benchmarksgame/
 *
 * Contributed by Troestler Christophe
 *
 * Uses: knucleotide
 * Usage: ./knucleotide < input.txt
 *
 * For testing without input file:
 *   ./knucleotide  (uses generated data)
 *)

module Tbl = Hashtbl

let generate_test_data () =
  let dna = Buffer.create 10000 in
  let bases = "ACGT" in
  Random.init 42;
  for _ = 1 to 10000 do
    Buffer.add_char dna bases.[Random.int 4]
  done;
  Buffer.contents dna

let read_input () =
  let buf = Buffer.create 100000 in
  let in_seq = ref false in
  try
    while true do
      let line = input_line stdin in
      if String.length line > 0 && line.[0] = '>' then
        in_seq := String.length line > 6 && String.sub line 0 6 = ">THREE"
      else if !in_seq then
        Buffer.add_string buf (String.uppercase_ascii line)
    done;
    assert false
  with End_of_file ->
    if Buffer.length buf = 0 then generate_test_data ()
    else Buffer.contents buf

let count dna len =
  let tbl = Tbl.create 16 in
  let n = String.length dna - len + 1 in
  for i = 0 to n - 1 do
    let key = String.sub dna i len in
    let c = try Tbl.find tbl key with Not_found -> 0 in
    Tbl.replace tbl key (c + 1)
  done;
  tbl

let print_frequencies dna len =
  let tbl = count dna len in
  let total = float (String.length dna - len + 1) in
  let pairs = Tbl.fold (fun k v acc -> (k, v) :: acc) tbl [] in
  let sorted = List.sort (fun (_, v1) (_, v2) -> compare v2 v1) pairs in
  List.iter (fun (k, v) ->
    Printf.printf "%s %.3f\n" k (100. *. float v /. total)
  ) sorted;
  print_newline ()

let print_count dna seq =
  let tbl = count dna (String.length seq) in
  let c = try Tbl.find tbl seq with Not_found -> 0 in
  Printf.printf "%d\t%s\n" c seq

let () =
  let dna = read_input () in
  print_frequencies dna 1;
  print_frequencies dna 2;
  print_count dna "GGT";
  print_count dna "GGTA";
  print_count dna "GGTATT";
  print_count dna "GGTATTTTAATT";
  print_count dna "GGTATTTTAATTTATAGT"
