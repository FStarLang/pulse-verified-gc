(* Forces the major mark's gray stack to overflow, so the heap rescan runs.
 *
 *   usage: ocamlrun ./gray_overflow.byte <major-heap-words>
 *   with MIN_EXPANSION_WORDSIZE set to the same word count.
 *   Exit 0: every object survived with its contents. Exit 1: one did not.
 *
 * The verified runtime sizes the gray stack at major_bytes / 64, i.e.
 * heap_words / 8 entries (verified_gc/alloc_gen.c).  [a] below holds
 * heap_words / 5 distinct, freshly promoted refs, so when the mark pops [a]
 * it finds more white children than the stack can hold: the excess is grayed
 * but not pushed, and only the rescan finds them again.  The mark skips the
 * rescan when the stack never overflowed; if it ever skipped it here, those
 * refs would stay gray, the sweep would free them (it frees everything not
 * black), and [b]'s refs would be allocated over them -- which the final
 * check sees.
 *
 * Differential, like the other correctness tests: it must pass under stock
 * OCaml too.
 *)

let heap_words = int_of_string Sys.argv.(1)
let n = heap_words / 5
let cap = heap_words / 8
(* As many refs as the mark drops: enough to cover what a skipped rescan frees. *)
let m = n - cap

let check a =
  let bad = ref 0 in
  Array.iteri (fun i r -> if !r <> i then incr bad) a;
  !bad

let () =
  (* > Max_young_wosize, so [a] itself is allocated in the major heap *)
  let a = Array.make n (ref (-1)) in
  for i = 0 to n - 1 do a.(i) <- ref i done;
  (* The minor collection inside promotes the refs; the major mark then pops
     [a] with n white children against a stack of heap_words / 8. *)
  Gc.full_major ();
  (* Reuse whatever the collection freed. *)
  let b = Array.make m (ref (-1)) in
  for i = 0 to m - 1 do b.(i) <- ref (-1 - i) done;
  Gc.full_major ();
  let bad = check a in
  Printf.printf "gray_overflow: %d refs, gray stack %d entries, %d wrong\n%!"
    n cap bad;
  ignore (Sys.opaque_identity b);
  exit (if bad = 0 then 0 else 1)
