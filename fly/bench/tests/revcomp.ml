(*
 * The Computer Language Benchmarks Game
 * https://salsa.debian.org/benchmarksgame-team/benchmarksgame/
 *
 * Contributed by Troestler Christophe
 *
 * Uses: revcomp (reverse-complement)
 * Usage: ./revcomp < input.txt
 *
 * For testing without input file:
 *   ./revcomp  (uses generated data)
 *)

let complement =
  let tbl = Bytes.make 256 '\000' in
  List.iter (fun (a, b) ->
    Bytes.set tbl (Char.code a) b;
    Bytes.set tbl (Char.code (Char.lowercase_ascii a)) b
  ) [ ('A', 'T'); ('T', 'A'); ('C', 'G'); ('G', 'C');
      ('U', 'A'); ('M', 'K'); ('R', 'Y'); ('W', 'W');
      ('S', 'S'); ('Y', 'R'); ('K', 'M'); ('V', 'B');
      ('H', 'D'); ('D', 'H'); ('B', 'V'); ('N', 'N') ];
  Bytes.to_string tbl

let rev_comp_in_place buf =
  let len = Bytes.length buf in
  let i = ref 0 and j = ref (len - 1) in
  while !i < !j do
    let ci = Bytes.get buf !i in
    let cj = Bytes.get buf !j in
    Bytes.set buf !i complement.[Char.code cj];
    Bytes.set buf !j complement.[Char.code ci];
    incr i; decr j
  done;
  if !i = !j then
    Bytes.set buf !i complement.[Char.code (Bytes.get buf !i)]

let print_lines buf =
  let len = Bytes.length buf in
  let width = 60 in
  let i = ref 0 in
  while !i < len do
    let cnt = min width (len - !i) in
    print_bytes (Bytes.sub buf !i cnt);
    print_char '\n';
    i := !i + cnt
  done

let generate_test_data () =
  let bases = "ACGTMRWSYKVHDBN" in
  Random.init 42;
  let out = Buffer.create 1000 in
  Buffer.add_string out ">ONE Homo sapiens alu\n";
  for _ = 1 to 500 do
    Buffer.add_char out bases.[Random.int (String.length bases)]
  done;
  Buffer.contents out

let () =
  let lines = 
    try
      let buf = Buffer.create 100000 in
      try
        while true do
          Buffer.add_string buf (input_line stdin);
          Buffer.add_char buf '\n'
        done;
        assert false
      with End_of_file -> Buffer.contents buf
    with _ -> generate_test_data ()
  in
  
  let seqs = Str.split (Str.regexp ">") lines in
  List.iter (fun seq ->
    if String.length seq > 0 then begin
      let newline_pos = try String.index seq '\n' with Not_found -> String.length seq in
      let header = String.sub seq 0 newline_pos in
      let data = String.sub seq (newline_pos + 1) (String.length seq - newline_pos - 1) in
      let data = Str.global_replace (Str.regexp "\n") "" data in
      let buf = Bytes.of_string data in
      rev_comp_in_place buf;
      Printf.printf ">%s\n" header;
      print_lines buf
    end
  ) seqs
