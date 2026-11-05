(* A large random graph kept live: n nodes, each with d random out-edges
   (stored in a per-node array), rewired over several rounds.
   Benchmark for the major mark: `livegraph.byte 1000000 4 4` with
   MIN_EXPANSION_WORDSIZE=16777216 (see `make bench-mark`). *)
type node = { id : int; mutable out : node array; mutable w : float }
let () =
  let n = try int_of_string Sys.argv.(1) with _ -> 1_000_000 in
  let d = try int_of_string Sys.argv.(2) with _ -> 4 in
  let rounds = try int_of_string Sys.argv.(3) with _ -> 4 in
  Random.init 42;
  let nodes = Array.init n (fun id -> { id; out = [||]; w = 0.0 }) in
  Array.iter (fun x -> x.out <- Array.init d (fun _ -> nodes.(Random.int n))) nodes;
  for _ = 1 to rounds do
    for i = 0 to n / 2 do
      let x = nodes.(Random.int n) in
      x.out <- Array.init d (fun _ -> nodes.(Random.int n));
      x.w <- x.w +. 1.0
    done
  done;
  let s = ref 0 in
  Array.iter (fun x -> s := !s + x.out.(0).id) nodes;
  Printf.printf "%d\n" (!s mod 1000)
