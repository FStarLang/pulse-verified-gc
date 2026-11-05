(* Regression test for issue #34: a minor collection aborted when the major
 * heap was full of garbage left by large (direct major) allocations.
 *
 *   usage: ocamlrun ./large_alloc_garbage.byte <major-heap-words> <leave-free>
 *   with MIN_EXPANSION_WORDSIZE set to the same word count.
 *   Exit 0: the program completed. Exit 1: Out_of_memory was raised, or the
 *   result is wrong. Before the fix the runtime aborted with
 *   "verified gen GC: out of memory (major heap too small)" (exit 134).
 *
 * Differential, like the other correctness tests: it must pass under stock
 * OCaml too.
 *
 * Arrays larger than Max_young_wosize go straight to the major heap through
 * verified_allocate and are dropped at once, so the heap fills with garbage
 * while no minor collection runs. The full-collection trigger counted only
 * promoted bytes, so nothing collected that garbage, and the next minor
 * collection had nowhere to promote a small young live set. Direct major
 * allocations now count toward the trigger, and verified_allocate runs a full
 * collection itself once they pass half the heap.
 *)

let heap_words = int_of_string Sys.argv.(1)
let leave_free = int_of_string Sys.argv.(2)
let chunk = 10_000
let sink = ref [||]

let () =
  let n = (heap_words - leave_free) / (chunk + 1) in
  for _ = 1 to n do sink := Array.make chunk 0 done;   (* each one dead next round *)
  sink := [||];
  Printf.printf "filled %d dead arrays of %d words\n%!" n chunk;
  let r =
    try
      (* 60k cons = 180k words of live young data, < 256k-word nursery *)
      let rec build acc n = if n = 0 then acc else build (n :: acc) (n - 1) in
      let live = build [] 60_000 in
      (* churn young garbage to force minor collections that promote [live] *)
      for i = 1 to 2_000_000 do ignore (Sys.opaque_identity (ref i)) done;
      Ok (List.fold_left (+) 0 live)
    with Out_of_memory -> Error "Out_of_memory"
  in
  match r with
  | Ok 1_800_030_000 -> print_endline "ok, sum=1800030000"
  | Ok s -> Printf.printf "FAIL: sum=%d, expected 1800030000\n" s; exit 1
  | Error e -> Printf.printf "FAIL: %s\n" e; exit 1
