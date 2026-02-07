(* binarytrees.ml - Classic GC stress test from Computer Language Benchmarks Game
 * Creates many short-lived tree nodes, stressing allocation and GC
 * Usage: ./binarytrees <depth>  (default: 21)
 *)

type tree = Empty | Node of tree * tree

let rec make d =
  if d = 0 then Node(Empty, Empty)
  else let d = d - 1 in Node(make d, make d)

let rec check = function
  | Empty -> 0
  | Node(l, r) -> 1 + check l + check r

let min_depth = 4

let () =
  let n = try int_of_string Sys.argv.(1) with _ -> 21 in
  let max_depth = max (min_depth + 2) n in
  let stretch_depth = max_depth + 1 in
  
  let c = check (make stretch_depth) in
  Printf.printf "stretch tree of depth %i\t check: %i\n" stretch_depth c;
  
  let long_lived_tree = make max_depth in
  
  for d = 0 to (max_depth - min_depth) / 2 do
    let d = min_depth + d * 2 in
    let niter = 1 lsl (max_depth - d + min_depth) in
    let c = ref 0 in
    for _ = 1 to niter do
      c := !c + check (make d)
    done;
    Printf.printf "%i\t trees of depth %i\t check: %i\n" niter d !c
  done;
  
  Printf.printf "long lived tree of depth %i\t check: %i\n"
    max_depth (check long_lived_tree)
