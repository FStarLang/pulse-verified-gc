(* Keeps a large Map live (n entries, each a boxed record) and churns
   short-lived garbage while inserting, then does lookups/updates rounds.
   Benchmark for the major mark: `livemap.byte 1000000 1` with
   MIN_EXPANSION_WORDSIZE=25165824 (see `make bench-mark`). *)
module M = Map.Make (Int)
type r = { k : int; mutable v : int list }
let () =
  let n = try int_of_string Sys.argv.(1) with _ -> 1_000_000 in
  let rounds = try int_of_string Sys.argv.(2) with _ -> 3 in
  let m = ref M.empty in
  let junk = ref [] in
  for i = 0 to n - 1 do
    let k = (i * 7919) mod n in
    m := M.add k { k; v = [ i ] } !m;
    junk := [ i; i + 1 ];
  done;
  for r = 1 to rounds do
    for i = 0 to n - 1 do
      let k = (i * 104729 + r) mod n in
      (match M.find_opt k !m with
       | Some x -> x.v <- [ r ]
       | None -> ());
      if i mod 4 = 0 then m := M.add k { k; v = [ r; i ] } !m
    done
  done;
  ignore !junk;
  Printf.printf "%d\n" (M.cardinal !m)
