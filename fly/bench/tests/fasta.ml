(*
 * The Computer Language Benchmarks Game
 * https://salsa.debian.org/benchmarksgame-team/benchmarksgame/
 *
 * contributed by Troestler Christophe
 *
 * Usage: ./fasta <n>  (default: 25_000_000)
 *)

let im = 139968
and ia = 3877
and ic = 29573

let last = ref 42

let gen_random max =
  last := (!last * ia + ic) mod im;
  max *. float !last /. float im

let alu = "GGCCGGGCGCGGTGGCTCACGCCTGTAATCCCAGCACTTTGG\
GAGGCCGAGGCGGGCGGATCACCTGAGGTCAGGAGTTCGAGA\
CCAGCCTGGCCAACATGGTGAAACCCCGTCTCTACTAAAAAT\
ACAAAAATTAGCCGGGCGTGGTGGCGCGCGCCTGTAATCCCA\
GCTACTCGGGAGGCTGAGGCAGGAGAATCGCTTGAACCCGGG\
AGGCGGAGGTTGCAGTGAGCCGAGATCGCGCCACTGCACTCC\
AGCCTGGGCGACAGAGCGAGACTCCGTCTCAAAAA"

let iub = [| ('a', 0.27); ('c', 0.12); ('g', 0.12); ('t', 0.27);
             ('B', 0.02); ('D', 0.02); ('H', 0.02); ('K', 0.02);
             ('M', 0.02); ('N', 0.02); ('R', 0.02); ('S', 0.02);
             ('V', 0.02); ('W', 0.02); ('Y', 0.02) |]

let homosapiens = [| ('a', 0.3029549426680);
                     ('c', 0.1979883004921);
                     ('g', 0.1975473066391);
                     ('t', 0.3015094502008) |]

let make_cumulative table =
  let prob = ref 0. in
  Array.map (fun (c, p) -> prob := !prob +. p; (c, !prob)) table

let select_random table =
  let r = gen_random 1.0 in
  let rec find i =
    if i >= Array.length table - 1 then fst table.(i)
    else if r < snd table.(i) then fst table.(i)
    else find (i + 1)
  in
  find 0

let width = 60

let make_repeat_fasta id desc src n =
  Printf.printf ">%s %s\n" id desc;
  let len = String.length src in
  let src = src ^ src in
  let i = ref 0 in
  let m = ref n in
  while !m > 0 do
    let cnt = min !m width in
    print_string (String.sub src !i cnt);
    print_char '\n';
    i := (!i + cnt) mod len;
    m := !m - cnt
  done

let make_random_fasta id desc table n =
  Printf.printf ">%s %s\n" id desc;
  let buf = Bytes.create (width + 1) in
  Bytes.set buf width '\n';
  let m = ref n in
  while !m > 0 do
    let cnt = min !m width in
    for i = 0 to cnt - 1 do
      Bytes.set buf i (select_random table)
    done;
    if cnt < width then begin
      Bytes.set buf cnt '\n';
      print_bytes (Bytes.sub buf 0 (cnt + 1))
    end else
      print_bytes buf;
    m := !m - cnt
  done

let () =
  let n = try int_of_string Sys.argv.(1) with _ -> 25_000_000 in
  make_repeat_fasta "ONE" "Homo sapiens alu" alu (n * 2);
  make_random_fasta "TWO" "IUB ambiguity codes" (make_cumulative iub) (n * 3);
  make_random_fasta "THREE" "Homo sapiens frequency" (make_cumulative homosapiens) (n * 5)
