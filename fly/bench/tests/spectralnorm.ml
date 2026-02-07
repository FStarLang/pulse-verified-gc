(*
 * The Computer Language Benchmarks Game
 * https://salsa.debian.org/benchmarksgame-team/benchmarksgame/
 *
 * Contributed by Sebastien Loisel
 * Cleanup by Troestler Christophe
 *
 * Usage: ./spectralnorm <n>  (default: 5500)
 *)

let eval_a i j = 1. /. float ((i + j) * (i + j + 1) / 2 + i + 1)

let eval_a_times_u u v =
  let n = Array.length v in
  for i = 0 to n - 1 do
    let vi = ref 0. in
    for j = 0 to n - 1 do
      vi := !vi +. eval_a i j *. u.(j)
    done;
    v.(i) <- !vi
  done

let eval_at_times_u u v =
  let n = Array.length v in
  for i = 0 to n - 1 do
    let vi = ref 0. in
    for j = 0 to n - 1 do
      vi := !vi +. eval_a j i *. u.(j)
    done;
    v.(i) <- !vi
  done

let eval_ata_times_u u v =
  let w = Array.make (Array.length u) 0. in
  eval_a_times_u u w;
  eval_at_times_u w v

let () =
  let n = try int_of_string Sys.argv.(1) with _ -> 5500 in
  let u = Array.make n 1. and v = Array.make n 0. in
  for _ = 0 to 9 do
    eval_ata_times_u u v;
    eval_ata_times_u v u
  done;
  let vv = ref 0. and vbv = ref 0. in
  for i = 0 to n - 1 do
    vv := !vv +. v.(i) *. v.(i);
    vbv := !vbv +. u.(i) *. v.(i)
  done;
  Printf.printf "%.9f\n" (sqrt (!vbv /. !vv))
